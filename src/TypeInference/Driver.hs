module TypeInference.Driver (inferProgram, insertDecl, execDriverM) where

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

import Control.Monad.State
import Control.Monad.Except


---------------------------------------------------------------------------------
-- Typeinference Driver Monad
---------------------------------------------------------------------------------

data DriverState = DriverState
  { driverOpts :: InferenceOptions
  , driverEnv :: Environment FreeVarName
  }

newtype DriverM a = DriverM { unDriverM :: StateT DriverState  (ExceptT LocatedError IO) a }
  deriving (Functor, Applicative, Monad, MonadError LocatedError, MonadState DriverState, MonadIO)

execDriverM :: DriverState ->  DriverM a -> IO (Either LocatedError (a,DriverState))
execDriverM state act = runExceptT $ runStateT (unDriverM act) state

---------------------------------------------------------------------------------
-- Utility functions
---------------------------------------------------------------------------------

setEnvironment :: Environment FreeVarName -> DriverM ()
setEnvironment env = modify (\state -> state { driverEnv = env })

-- | Only execute an action if verbosity is set to Verbose
guardVerbose :: IO () -> DriverM ()
guardVerbose action = do
    verbosity <- gets (infOptsVerbosity . driverOpts)
    when (verbosity == Verbose) (liftIO action)

-- | Given the Library Paths contained in the inference options and a module name,
-- try to find a filepath which corresponds to the given module name.
findModule :: ModuleName -> Loc ->  DriverM FilePath
findModule (ModuleName mod) loc = do
  infopts <- gets driverOpts
  let libpaths = infOptsLibPath infopts
  fps <- forM libpaths $ \libpath -> do
    let fp = libpath </> T.unpack mod <.> "ds"
    exists <- liftIO $ doesFileExist fp
    if exists then return [fp] else return []
  case concat fps of
    [] -> throwError (Located loc (OtherError ("Could not locate library: " <> mod)))
    (fp:_) -> return fp

checkAnnot :: TypeScheme pol -- ^ Inferred type
           -> Maybe (TypeScheme pol) -- ^ Annotated type
           -> Loc -- ^ Location for the error message
           -> DriverM (TypeScheme pol)
checkAnnot tyInferred Nothing _ = return tyInferred
checkAnnot tyInferred (Just tyAnnotated) loc = do
  let isSubsumed = subsume tyInferred tyAnnotated
  case isSubsumed of
      (Left err) -> throwError (Located loc err)
      (Right True) -> return tyAnnotated
      (Right False) -> do
        let err = OtherError $ T.unlines [ "Annotated type is not subsumed by inferred type"
                                         , " Annotated type: " <> ppPrint tyAnnotated
                                         , " Inferred type:  " <> ppPrint tyInferred
                                         ]
        guardVerbose $ ppPrintIO err
        throwError (Located loc err)

---------------------------------------------------------------------------------
-- Insert Declarations
---------------------------------------------------------------------------------

insertDecl :: Declaration FreeVarName Loc
           -> DriverM ()
insertDecl (PrdDecl isRec loc v annot loct) = do
  infopts <- gets driverOpts
  env <- gets driverEnv
  case inferSTermTraced isRec loc v infopts PrdRep loct env of
    Left err -> do
      let locerr = Located loc err
      guardVerbose $ printLocatedError locerr
      throwError locerr
    Right trace -> do
      guardVerbose $ ppPrintIO (trace_constraintSet trace)
      guardVerbose $ ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation
      ty <- checkAnnot (trace_resType trace) annot loc
      let newEnv = env { prdEnv  = M.insert v ( first (const ()) loct ,loc, ty) (prdEnv env) }
      guardVerbose $ putStr "Inferred type: " >> ppPrintIO (trace_resType trace)
      setEnvironment newEnv
insertDecl (CnsDecl isRec loc v annot loct) = do
  infopts <- gets driverOpts
  env <- gets driverEnv
  case inferSTermTraced isRec loc v infopts CnsRep loct env of
    Left err -> do
      let locerr = Located loc err
      guardVerbose $ printLocatedError locerr
      throwError locerr
    Right trace -> do
      guardVerbose $ ppPrintIO (trace_constraintSet trace)
      guardVerbose $ ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation:
      ty <- checkAnnot (trace_resType trace) annot loc
      let newEnv = env { cnsEnv  = M.insert v (first (const ()) loct, loc, ty) (cnsEnv env) }
      guardVerbose $ putStr "Inferred type: " >> ppPrintIO (trace_resType trace)
      setEnvironment newEnv
insertDecl (CmdDecl loc v loct) = do
  infopts <- gets driverOpts
  env <- gets driverEnv
  case checkCmd loct env infopts of
    Left err -> do
      let locerr = Located loc err
      guardVerbose $ printLocatedError locerr
      throwError locerr
    Right (constraints, solverResult) -> do
      guardVerbose $ ppPrintIO constraints
      guardVerbose $ ppPrintIO solverResult
      let newEnv = env { cmdEnv  = M.insert v (first (const ()) loct, loc) (cmdEnv env)}
      setEnvironment newEnv
insertDecl (DefDecl isRec loc v annot t) = do
  infopts <- gets driverOpts
  env <- gets driverEnv
  case inferATermTraced isRec loc v infopts t env of
    Left err -> do
      let locerr = Located loc err
      guardVerbose $ printLocatedError locerr
      throwError locerr
    Right trace -> do
      guardVerbose $ ppPrintIO (trace_constraintSet trace)
      guardVerbose $ ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation
      ty <- checkAnnot (trace_resType trace) annot loc
      let newEnv = env { defEnv  = M.insert v (first (const ()) t, loc,ty) (defEnv env)}
      guardVerbose $ putStr "Inferred type: " >> ppPrintIO (trace_resType trace)
      setEnvironment newEnv
insertDecl (DataDecl _loc dcl) = do
  env <- gets driverEnv
  let newEnv = env { declEnv = dcl : declEnv env}
  setEnvironment newEnv
insertDecl (ImportDecl loc mod) = do
  fp <- findModule mod loc
  inferProgramFromDisk fp
insertDecl ParseErrorDecl = do
    throwError (Located undefined (OtherError "Should not occur: Tried to insert ParseErrorDecl into Environment"))


inferProgramFromDisk :: FilePath
                     -> DriverM ()
inferProgramFromDisk fp = do
  file <- liftIO $ T.readFile fp
  let parsed = runFileParser fp programP file
  case parsed of
    Left _err -> throwError (Located undefined undefined)
    Right decls -> inferProgram decls

inferProgram :: [Declaration FreeVarName Loc]
             -> DriverM ()
inferProgram decls = forM_ decls insertDecl


