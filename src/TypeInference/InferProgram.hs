module TypeInference.InferProgram
  ( TypeInferenceTrace (..)
  , InferenceOptions(..)
  , defaultInferenceOptions
    -- Symmetric Terms and Commands
  , inferSTermTraced
  , inferSTerm
    -- Asymmetric terms
  , inferATerm
    -- Declarations and Programs
  , insertDecl
  , inferProgram
  ) where

import Control.Monad (when)
import Data.Bifunctor (first)
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as T

import Errors ( LocatedError, Error(OtherError) )
import Pretty.Pretty ( ppPrint, ppPrintIO )
import Pretty.Errors ( printLocatedError )
import Syntax.ATerms ( FreeVarName, PrdCnsRep(..), ATerm )
import Syntax.STerms ( FreeVarName, PrdCnsRep(..), Command, STerm )
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
      ModuleName(ModuleName) )
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

------------------------------------------------------------------------------
-- Typeinference Options
------------------------------------------------------------------------------

data InferenceOptions = InferenceOptions
  { infOptsVerbosity :: Verbosity
  , infOptsMode :: InferenceMode
  , infOptsLibPath :: Maybe FilePath 
  }

defaultInferenceOptions :: InferenceOptions
defaultInferenceOptions = InferenceOptions Silent InferNominal Nothing

------------------------------------------------------------------------------
-- TypeInference Trace
------------------------------------------------------------------------------

data TypeInferenceTrace pol = TypeInferenceTrace
  { trace_constraintSet :: ConstraintSet
  , trace_solvedConstraints :: SolverResult
  , trace_typeAut :: TypeAut pol
  , trace_typeAutDet :: TypeAutDet pol
  , trace_typeAutDetAdms :: TypeAutDet pol
  , trace_minTypeAut :: TypeAutDet pol
  , trace_resType :: TypeScheme pol
  }

generateTypeInferenceTrace :: PolarityRep pol
                           -> ConstraintSet
                           -> SolverResult
                           -> Typ pol
                           -> Either Error (TypeInferenceTrace pol)
generateTypeInferenceTrace rep constraintSet solverState typ = do
  typeAut <- solverStateToTypeAut solverState rep typ
  lint typeAut
  let typeAutDet = determinize typeAut
  lint typeAutDet
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  lint typeAutDetAdms
  let minTypeAut = minimize typeAutDetAdms
  lint minTypeAut
  resType <- autToType minTypeAut
  return TypeInferenceTrace
    { trace_constraintSet = constraintSet
    , trace_solvedConstraints = solverState
    , trace_typeAut = typeAut
    , trace_typeAutDet = typeAutDet
    , trace_typeAutDetAdms = typeAutDetAdms
    , trace_minTypeAut = minTypeAut
    , trace_resType = resType
    }

------------------------------------------------------------------------------
-- Symmetric Terms and Commands
------------------------------------------------------------------------------

inferSTermTraced :: IsRec
                 -> Loc
                 -> FreeVarName
                 -> InferenceOptions
                 -> PrdCnsRep pc -> STerm pc Loc FreeVarName
                 -> Environment FreeVarName
                 -> Either Error (TypeInferenceTrace (PrdCnsToPol pc))
inferSTermTraced isRec loc fv infopts rep tm env = do
  let genFun = case isRec of
        Recursive -> genConstraintsSTermRecursive loc fv rep tm
        NonRecursive -> genConstraintsSTerm tm
  ((_,ty), constraintSet) <- runGenM env (infOptsMode infopts) genFun
  solverState <- solveConstraints constraintSet env (infOptsMode infopts)
  generateTypeInferenceTrace (prdCnsToPol rep) constraintSet solverState ty

inferSTerm :: IsRec
           -> Loc
           -> FreeVarName
           -> InferenceOptions
           -> PrdCnsRep pc -> STerm pc Loc FreeVarName
           -> Environment FreeVarName
           -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTerm isRec loc fv infopts rep tm env = do
  trace <- inferSTermTraced isRec loc fv infopts rep tm env
  return $ trace_resType trace

checkCmd :: Command Loc FreeVarName
         -> Environment FreeVarName
         -> InferenceOptions
         -> Either Error (ConstraintSet, SolverResult)
checkCmd cmd env infopts = do
  constraints <- snd <$> runGenM env (infOptsMode infopts) (genConstraintsCommand cmd)
  solverResult <- solveConstraints constraints env (infOptsMode infopts)
  return (constraints, solverResult)

------------------------------------------------------------------------------
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATermTraced :: IsRec
                 -> Loc
                 -> FreeVarName
                 -> InferenceOptions
                 -> ATerm Loc FreeVarName
                 -> Environment FreeVarName
                 -> Either Error (TypeInferenceTrace Pos)
inferATermTraced isRec loc fv infopts tm env = do
  let genFun = case isRec of
        Recursive -> genConstraintsATermRecursive loc fv tm
        NonRecursive -> genConstraintsATerm tm
  ((_, ty), constraintSet) <- runGenM env (infOptsMode infopts) genFun
  solverState <- solveConstraints constraintSet env (infOptsMode infopts)
  generateTypeInferenceTrace PosRep constraintSet solverState ty

inferATerm :: IsRec
           -> Loc
           -> FreeVarName
           -> InferenceOptions
           -> ATerm Loc FreeVarName
           -> Environment FreeVarName
           -> Either Error (TypeScheme Pos)
inferATerm isRec loc fv infopts tm env = do
  trace <- inferATermTraced isRec loc fv infopts tm env
  return $ trace_resType trace

------------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------------

checkAnnot :: TypeScheme pol -- ^ Inferred type
           -> Maybe (TypeScheme pol) -- ^ Annotated type
           -> Either Error (TypeScheme pol)
checkAnnot tyInferred Nothing = return tyInferred
checkAnnot tyInferred (Just tyAnnotated) = do
  isSubsumed <- subsume tyInferred tyAnnotated
  if isSubsumed
    then return tyAnnotated
    else Left (OtherError (T.unlines [ "Annotated type is not subsumed by inferred type"
                                     , " Annotated type: " <> ppPrint tyAnnotated
                                     , " Inferred type:  " <> ppPrint tyInferred
                                     ]))


insertDecl :: InferenceOptions
           -> Declaration FreeVarName Loc
           -> Environment FreeVarName
           -> IO (Either LocatedError (Environment FreeVarName))
insertDecl infopts (PrdDecl isRec loc v annot loct)  env@Environment { prdEnv }  = do
  case inferSTermTraced isRec loc v infopts PrdRep loct env of
    Left err -> do
      let locerr = Located loc err
      printLocatedError locerr
      return (Left locerr)
    Right trace -> do
      when (infOptsVerbosity infopts == Verbose) $ do
        ppPrintIO (trace_constraintSet trace)
        ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation
      let ty = trace_resType trace
      case checkAnnot ty annot of
        Left err -> do
           ppPrintIO err
           return (Left (Located loc err))
        Right ty -> do
          let newEnv = env { prdEnv  = M.insert v ( first (const ()) loct ,loc, ty) prdEnv }
          putStr "Inferred type: "
          ppPrintIO (trace_resType trace)
          return (Right newEnv)
insertDecl infopts (CnsDecl isRec loc v annot loct)  env@Environment { cnsEnv }  = do
  case inferSTermTraced isRec loc v infopts CnsRep loct env of
    Left err -> do
      let locerr = Located loc err
      printLocatedError locerr
      return (Left locerr)
    Right trace -> do
      when (infOptsVerbosity infopts == Verbose) $ do
        ppPrintIO (trace_constraintSet trace)
        ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation:
      let ty = trace_resType trace
      case checkAnnot ty annot of
        Left err -> do
          ppPrintIO err
          return (Left (Located loc err))
        Right ty -> do
          let newEnv = env { cnsEnv  = M.insert v (first (const ()) loct, loc, ty) cnsEnv }
          putStr "Inferred type: "
          ppPrintIO (trace_resType trace)
          return (Right newEnv)
insertDecl infopts (CmdDecl loc v loct)  env@Environment { cmdEnv }  = do
  case checkCmd loct env infopts of
    Left err -> do
      let locerr = Located loc err
      printLocatedError locerr
      return (Left locerr)
    Right (constraints, solverResult) -> do
      when (infOptsVerbosity infopts == Verbose) $ do
        ppPrintIO constraints
        ppPrintIO solverResult
      return (Right (env { cmdEnv  = M.insert v (first (const ()) loct, loc) cmdEnv }))
insertDecl infopts (DefDecl isRec loc v annot t)  env@Environment { defEnv }  = do
  case inferATermTraced isRec loc v infopts t env of
    Left err -> do
      let locerr = Located loc err
      printLocatedError locerr
      return (Left locerr)
    Right trace -> do
      when (infOptsVerbosity infopts == Verbose) $ do
        ppPrintIO (trace_constraintSet trace)
        ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation
      let ty = trace_resType trace
      case checkAnnot ty annot of
        Left err -> do
          ppPrintIO err
          return (Left (Located loc err))
        Right ty -> do
          let newEnv = env { defEnv  = M.insert v (first (const ()) t, loc,ty) defEnv }
          putStr "Inferred type: "
          ppPrintIO (trace_resType trace)
          return (Right newEnv)
insertDecl _ (DataDecl _loc dcl) env@Environment { declEnv } = do
  return (Right (env { declEnv = dcl : declEnv }))
insertDecl infopts (ImportDecl _loc (ModuleName mod)) env = do
  let fp = T.unpack mod <> ".ds"
  env' <- inferProgramFromDisk infopts fp
  case env' of
    Left err -> return (Left err)
    Right env' -> return (Right (env <> env'))
insertDecl _ ParseErrorDecl _ = error "Should not occur: Tried to insert ParseErrorDecl into Environment"



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


