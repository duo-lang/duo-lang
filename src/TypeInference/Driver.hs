module TypeInference.Driver where

import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist )
import Text.Megaparsec hiding (Pos)

import Errors ( LocatedError, Error(OtherError) )
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint, ppPrintIO )
import Pretty.Errors ( printLocatedError )
import Syntax.STerms ( Command, STerm, getTypeSTerm )
import Syntax.Types
    ( SolverResult,
      ConstraintSet,
      TypeScheme,
      Typ,
      PolarityRep(PosRep),
      Polarity(Pos) )
import Syntax.Program
    ( Environment(..),
      Declaration(..),
      IsRec(..),
      ModuleName(..) )
import TypeAutomata.ToAutomaton ( solverStateToTypeAut )
import TypeAutomata.Definition ( TypeAutDet, TypeAut )
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
import Utils ( Verbosity(..), Located(Located), Loc, defaultLoc )
import Syntax.ATerms

------------------------------------------------------------------------------
-- Typeinference Options
------------------------------------------------------------------------------

data InferenceOptions = InferenceOptions
  { infOptsVerbosity :: Verbosity -- ^ Whether to print debug information to the terminal.
  , infOptsMode :: InferenceMode  -- ^ Whether to infer nominal or refinement types
  , infOptsLibPath :: [FilePath]  -- ^ Where to search for imported modules
  }

defaultInferenceOptions :: InferenceOptions
defaultInferenceOptions = InferenceOptions Silent InferNominal []


---------------------------------------------------------------------------------
-- Typeinference Driver Monad
---------------------------------------------------------------------------------

data DriverState = DriverState
  { driverOpts :: InferenceOptions
  , driverEnv :: Environment
  }

newtype DriverM a = DriverM { unDriverM :: StateT DriverState  (ExceptT LocatedError IO) a }
  deriving (Functor, Applicative, Monad, MonadError LocatedError, MonadState DriverState, MonadIO)

execDriverM :: DriverState ->  DriverM a -> IO (Either LocatedError (a,DriverState))
execDriverM state act = runExceptT $ runStateT (unDriverM act) state

---------------------------------------------------------------------------------
-- Utility functions
---------------------------------------------------------------------------------

setEnvironment :: Environment -> DriverM ()
setEnvironment env = modify (\state -> state { driverEnv = env })

-- | Only execute an action if verbosity is set to Verbose.
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

liftErr :: Loc -> Error -> DriverM a
liftErr loc err = do
    let locerr = Located loc err
    guardVerbose $ printLocatedError locerr
    throwError locerr

liftEitherErr :: Loc -> Either Error a -> DriverM a
liftEitherErr loc x = case x of
    Left err -> liftErr loc err
    Right res -> return res

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
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATermTraced :: IsRec
                 -> Loc
                 -> FreeVarName
                 -> ATerm Parsed
                 -> DriverM (TypeInferenceTrace Pos, ATerm Inferred)
inferATermTraced isRec loc fv tm = do
  infopts <- gets driverOpts
  env <- gets driverEnv
  -- Generate the constraints
  let genFun = case isRec of
        Recursive -> genConstraintsATermRecursive loc fv tm
        NonRecursive -> genConstraintsATerm tm
  (tmInferred, constraintSet) <- liftEitherErr loc $ runGenM env (infOptsMode infopts) genFun
  -- Solve the constraints
  solverState <- liftEitherErr loc $ solveConstraints constraintSet env (infOptsMode infopts)
  -- Generate result type
  trace <- liftEitherErr loc $ generateTypeInferenceTrace PosRep constraintSet solverState (getTypeATerm tmInferred)
  return (trace, tmInferred)

inferATerm :: IsRec
           -> Loc
           -> FreeVarName
           -> ATerm Parsed
           -> DriverM (TypeScheme Pos, ATerm Inferred)
inferATerm isRec loc fv tm = do
  (trace, tmInferred) <- inferATermTraced isRec loc fv tm
  return (trace_resType trace, tmInferred)

------------------------------------------------------------------------------
-- Symmetric Terms and Commands
------------------------------------------------------------------------------

inferSTermTraced :: IsRec
                 -> Loc
                 -> FreeVarName
                 -> PrdCnsRep pc -> STerm pc Parsed
                 -> DriverM (TypeInferenceTrace (PrdCnsToPol pc), STerm pc Inferred)
inferSTermTraced isRec loc fv rep tm = do
  infopts <- gets driverOpts
  env <- gets driverEnv
  -- Generate the constraints
  let genFun = case isRec of
        Recursive -> genConstraintsSTermRecursive loc fv rep tm
        NonRecursive -> genConstraintsSTerm tm
  (tmInferred, constraintSet) <- liftEitherErr loc $ runGenM env (infOptsMode infopts) genFun
  -- Solve the constraints
  solverState <- liftEitherErr loc $ solveConstraints constraintSet env (infOptsMode infopts)
  -- Generate result type
  trace <- liftEitherErr loc $ generateTypeInferenceTrace (prdCnsToPol rep) constraintSet solverState (getTypeSTerm tmInferred)
  return (trace, tmInferred)


inferSTerm :: IsRec
           -> Loc
           -> FreeVarName
           -> PrdCnsRep pc -> STerm pc Parsed
           -> DriverM (TypeScheme (PrdCnsToPol pc), STerm pc Inferred)
inferSTerm isRec loc fv rep tm = do
  (trace, tmInferred) <- inferSTermTraced isRec loc fv rep tm
  return (trace_resType trace, tmInferred)

checkCmd :: Loc
         -> Command Parsed
         -> DriverM (ConstraintSet, SolverResult, Command Inferred)
checkCmd loc cmd = do
  infopts <- gets driverOpts
  env <- gets driverEnv
  -- Generate the constraints
  (cmdInferred,constraints) <- liftEitherErr loc $ runGenM env (infOptsMode infopts) (genConstraintsCommand cmd)
  -- Solve the constraints
  solverResult <- liftEitherErr loc $ solveConstraints constraints env (infOptsMode infopts)
  return (constraints, solverResult, cmdInferred)

---------------------------------------------------------------------------------
-- Insert Declarations
---------------------------------------------------------------------------------

insertDecl :: Declaration Parsed
           -> DriverM ()
insertDecl (PrdDecl loc isRec v annot loct) = do
  -- Infer a type
  (trace, tmInferred) <- inferSTermTraced isRec loc v PrdRep loct
  guardVerbose $ do
      ppPrintIO (trace_constraintSet trace)
      ppPrintIO (trace_solvedConstraints trace)
      putStr "Inferred type: " >> ppPrintIO (trace_resType trace)
  -- Check whether annotation matches inferred type
  ty <- checkAnnot (trace_resType trace) annot loc
  -- Insert into environment
  env <- gets driverEnv
  let newEnv = env { prdEnv  = M.insert v (tmInferred ,loc, ty) (prdEnv env) }
  setEnvironment newEnv
insertDecl (CnsDecl loc isRec v annot loct) = do
  -- Infer a type
  (trace, tmInferred) <- inferSTermTraced isRec loc v CnsRep loct
  guardVerbose $ do
      ppPrintIO (trace_constraintSet trace)
      ppPrintIO (trace_solvedConstraints trace)
      putStr "Inferred type: " >> ppPrintIO (trace_resType trace)
  -- Check whether annotation matches inferred type
  ty <- checkAnnot (trace_resType trace) annot loc
  -- Insert into environment
  env <- gets driverEnv
  let newEnv = env { cnsEnv  = M.insert v (tmInferred, loc, ty) (cnsEnv env) }
  setEnvironment newEnv
insertDecl (CmdDecl loc v loct) = do
  -- Check whether command is typeable
  (constraints, solverResult, cmdInferred) <- checkCmd loc loct
  guardVerbose $ do
      ppPrintIO constraints
      ppPrintIO solverResult
  -- Insert into environment
  env <- gets driverEnv
  let newEnv = env { cmdEnv  = M.insert v (cmdInferred, loc) (cmdEnv env)}
  setEnvironment newEnv
insertDecl (DefDecl loc isRec v annot t) = do
  -- Infer a type
  (trace, tmInferred) <- inferATermTraced isRec loc v t
  guardVerbose $ do
      ppPrintIO (trace_constraintSet trace)
      ppPrintIO (trace_solvedConstraints trace)
      putStr "Inferred type: " >> ppPrintIO (trace_resType trace)
  -- Check whether annotation matches inferred type
  ty <- checkAnnot (trace_resType trace) annot loc
  -- Insert into environment
  env <- gets driverEnv
  let newEnv = env { defEnv  = M.insert v (tmInferred, loc,ty) (defEnv env)}
  setEnvironment newEnv
insertDecl (DataDecl loc dcl) = do
  -- Insert into environment
  -- TODO: Check data decls
  env <- gets driverEnv
  let newEnv = env { declEnv = (loc,dcl) : declEnv env}
  setEnvironment newEnv
insertDecl (ImportDecl loc mod) = do
  fp <- findModule mod loc
  oldEnv <- gets driverEnv
  newEnv <- inferProgramFromDisk fp
  setEnvironment (oldEnv <> newEnv)
insertDecl (SetDecl loc txt) = case T.unpack txt of
  "refined" -> modify (\DriverState { driverOpts, driverEnv} -> DriverState driverOpts { infOptsMode = InferRefined }driverEnv)
  _ -> throwError (Located loc (OtherError ("Unknown option: " <> txt)))
insertDecl ParseErrorDecl = do
    throwError (Located defaultLoc (OtherError "Should not occur: Tried to insert ParseErrorDecl into Environment"))


inferProgramFromDisk :: FilePath
                     -> DriverM Environment
inferProgramFromDisk fp = do
  file <- liftIO $ T.readFile fp
  let parsed = runFileParser fp programP file
  case parsed of
    Left err -> throwError (Located defaultLoc (OtherError (T.pack (errorBundlePretty err))))
    Right decls -> do
        -- Use inference options of parent? Probably not?
        x <- liftIO $ inferProgramIO  (DriverState defaultInferenceOptions mempty) decls
        case x of
            Left err -> throwError err
            Right env -> return env

inferProgram :: [Declaration Parsed]
             -> DriverM ()
inferProgram decls = forM_ decls insertDecl



inferProgramIO  :: DriverState -- ^ Initial State
                -> [Declaration Parsed]
                -> IO (Either LocatedError Environment)
inferProgramIO state decls = do
    x <- execDriverM state (inferProgram decls)
    case x of
        Left err -> return (Left err)
        Right (_,x) -> return (Right (driverEnv x))
