module TypeInference.Driver where

import Control.Monad (when, forM)
import Data.Bifunctor (first)
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist )

import Errors ( LocatedError, Error(OtherError) )
import Pretty.Pretty ( ppPrint, ppPrintIO )
import Pretty.Errors ( printLocatedError )
import Syntax.ATerms ( FreeVarName, PrdCnsRep(..), ATerm )
import Syntax.STerms ( Command, STerm )
import Syntax.Types
    ( SolverResult,
      ConstraintSet,
      TypeScheme,
      Typ,
      PolarityRep(PosRep),
      Polarity(Pos) )
import TypeAutomata.Definition ( TypeAutDet, TypeAut )
import Syntax.Program
    ( Environment(..),
      Declaration(..),
      IsRec(..),
      ModuleName(..) )
import Utils ( Verbosity(..), Located(Located), Loc )

import TypeAutomata.ToAutomaton ( solverStateToTypeAut )
import TypeAutomata.Determinize ( determinize )
import TypeAutomata.Lint (lint)
import TypeAutomata.Minimize ( minimize )
import TypeAutomata.FromAutomaton ( autToType )
import TypeAutomata.RemoveAdmissible ( removeAdmissableFlowEdges )
import TypeAutomata.Subsume (subsume)
import TypeInference.GenerateConstraints.Definition
    ( PrdCnsToPol, prdCnsToPol, InferenceMode(..), runGenM )
import TypeInference.GenerateConstraints.ATerms
    ( genConstraintsATerm, genConstraintsATermRecursive )
import TypeInference.GenerateConstraints.STerms
    ( genConstraintsSTerm,
      genConstraintsCommand,
      genConstraintsSTermRecursive )
import TypeInference.SolveConstraints (solveConstraints)
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import TypeInference.InferProgram


-- | Only execute an action if verbosity is set to Verbose
guardVerbose :: InferenceOptions -> IO () -> IO ()
guardVerbose infopts action = when (infOptsVerbosity infopts == Verbose) action

insertDecl :: InferenceOptions
           -> Declaration FreeVarName Loc
           -> Environment FreeVarName
           -> IO (Either LocatedError (Environment FreeVarName))
insertDecl infopts (PrdDecl isRec loc v annot loct)  env@Environment { prdEnv }  = do
  case inferSTermTraced isRec loc v infopts PrdRep loct env of
    Left err -> do
      let locerr = Located loc err
      guardVerbose infopts $ printLocatedError locerr
      return (Left locerr)
    Right trace -> do
      guardVerbose infopts $ ppPrintIO (trace_constraintSet trace)
      guardVerbose infopts $ ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation
      let ty = trace_resType trace
      case checkAnnot ty annot of
        Left err -> do
           guardVerbose infopts $ ppPrintIO err
           return (Left (Located loc err))
        Right ty -> do
          let newEnv = env { prdEnv  = M.insert v ( first (const ()) loct ,loc, ty) prdEnv }
          guardVerbose infopts $ putStr "Inferred type: " >> ppPrintIO (trace_resType trace)
          return (Right newEnv)
insertDecl infopts (CnsDecl isRec loc v annot loct)  env@Environment { cnsEnv }  = do
  case inferSTermTraced isRec loc v infopts CnsRep loct env of
    Left err -> do
      let locerr = Located loc err
      guardVerbose infopts $ printLocatedError locerr
      return (Left locerr)
    Right trace -> do
      guardVerbose infopts $ ppPrintIO (trace_constraintSet trace)
      guardVerbose infopts $ ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation:
      let ty = trace_resType trace
      case checkAnnot ty annot of
        Left err -> do
          guardVerbose infopts $ ppPrintIO err
          return (Left (Located loc err))
        Right ty -> do
          let newEnv = env { cnsEnv  = M.insert v (first (const ()) loct, loc, ty) cnsEnv }
          guardVerbose infopts $ putStr "Inferred type: " >> ppPrintIO (trace_resType trace)
          return (Right newEnv)
insertDecl infopts (CmdDecl loc v loct)  env@Environment { cmdEnv }  = do
  case checkCmd loct env infopts of
    Left err -> do
      let locerr = Located loc err
      guardVerbose infopts $ printLocatedError locerr
      return (Left locerr)
    Right (constraints, solverResult) -> do
      guardVerbose infopts $ ppPrintIO constraints
      guardVerbose infopts $ ppPrintIO solverResult
      return (Right (env { cmdEnv  = M.insert v (first (const ()) loct, loc) cmdEnv }))
insertDecl infopts (DefDecl isRec loc v annot t)  env@Environment { defEnv }  = do
  case inferATermTraced isRec loc v infopts t env of
    Left err -> do
      let locerr = Located loc err
      guardVerbose infopts $ printLocatedError locerr
      return (Left locerr)
    Right trace -> do
      guardVerbose infopts $ ppPrintIO (trace_constraintSet trace)
      guardVerbose infopts $ ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation
      let ty = trace_resType trace
      case checkAnnot ty annot of
        Left err -> do
          guardVerbose infopts $ ppPrintIO err
          return (Left (Located loc err))
        Right ty -> do
          let newEnv = env { defEnv  = M.insert v (first (const ()) t, loc,ty) defEnv }
          guardVerbose infopts $ putStr "Inferred type: " >> ppPrintIO (trace_resType trace)
          return (Right newEnv)
insertDecl _ (DataDecl _loc dcl) env@Environment { declEnv } = do
  return (Right (env { declEnv = dcl : declEnv }))
insertDecl infopts (ImportDecl loc mod) env = do
  mfp <- findModule infopts mod
  case mfp of
    Nothing -> return (Left (Located loc (OtherError ("Could not locate library: " <> unModuleName mod))))
    Just fp -> do
      env' <- inferProgramFromDisk infopts fp
      case env' of
        Left err -> return (Left err)
        Right env' -> return (Right (env <> env'))
insertDecl _ ParseErrorDecl _ = error "Should not occur: Tried to insert ParseErrorDecl into Environment"

-- | Given the Library Paths contained in the inference options and a module name,
-- try to find a filepath which corresponds to the given module name.
findModule :: InferenceOptions -> ModuleName -> IO (Maybe FilePath)
findModule infopts (ModuleName mod) = do
  let libpaths = infOptsLibPath infopts
  fps <- forM libpaths $ \libpath -> do
    let fp = libpath </> T.unpack mod <.> "ds"
    exists <- doesFileExist fp
    if exists then return [fp] else return []
  case concat fps of
    [] -> return Nothing 
    (fp:_) -> return (Just fp)
  


inferProgramFromDisk :: InferenceOptions
                     -> FilePath
                     -> IO (Either LocatedError (Environment FreeVarName ))
inferProgramFromDisk infopts fp = do
  file <- T.readFile fp
  let parsed = runFileParser fp programP file
  case parsed of
    Left _err -> return (Left (Located undefined undefined))
    Right decls -> inferProgram infopts decls

inferProgram :: InferenceOptions
             -> [Declaration FreeVarName Loc]
             -> IO (Either LocatedError (Environment FreeVarName))
inferProgram infopts decls = inferProgram' mempty decls
 where
   inferProgram' :: Environment FreeVarName
                 -> [Declaration FreeVarName Loc]
                 -> IO (Either LocatedError (Environment FreeVarName))
   inferProgram' env [] = return (Right env)
   inferProgram' env (decl:decls) = do
     env' <- insertDecl infopts decl env
     case env' of
       Left err -> return (Left err)
       Right env'' -> inferProgram' env'' decls

