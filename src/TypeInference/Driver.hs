module TypeInference.Driver
  ( InferenceOptions(..)
  , defaultInferenceOptions
  , DriverState(..)
  , execDriverM
  , inferProgramIO
  , inferDecl
  ) where

import Control.Monad.State
import Control.Monad.Except
import Data.GraphViz
    ( isGraphvizInstalled, runGraphviz, GraphvizOutput(XDot, Jpeg) )
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Text.IO qualified as T
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist, createDirectoryIfMissing, getCurrentDirectory)
import Text.Megaparsec hiding (Pos)


import Errors ( LocatedError, Error(OtherError) )
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint, ppPrintIO )
import Pretty.TypeAutomata (typeAutToDot)
import Pretty.Errors ( printLocatedError )
import Syntax.Terms
import Syntax.CommonTerm
import Syntax.Types
    ( TypeScheme,
      generalize,
    )
import Syntax.Program
    ( Program,
      Environment(..),
      Declaration(..),
      IsRec(..),
      ModuleName(..) )
import Syntax.Zonking (zonkType)
import TypeAutomata.Definition
import TypeAutomata.Simplify
import TypeAutomata.Subsume (subsume)
import TypeInference.Coalescing ( coalesce )
import TypeInference.GenerateConstraints.Definition
    ( InferenceMode(..), runGenM )
import TypeInference.GenerateConstraints.Terms
    ( genConstraintsTerm,
      genConstraintsCommand,
      genConstraintsTermRecursive )
import TypeInference.SolveConstraints (solveConstraints)
import Utils ( Verbosity(..), Located(Located), Loc, defaultLoc )


------------------------------------------------------------------------------
-- Typeinference Options
------------------------------------------------------------------------------

data InferenceOptions = InferenceOptions
  { infOptsVerbosity   :: Verbosity      -- ^ Whether to print debug information to the terminal.
  , infOptsPrintGraphs :: Bool           -- ^ Whether to print graphs from type simplification.
  , infOptsMode        :: InferenceMode  -- ^ Whether to infer nominal or refinement types.
  , infOptsSimplify    :: Bool           -- ^ Whether or not to simplify types.
  , infOptsLibPath     :: [FilePath]     -- ^ Where to search for imported modules.
  }

defaultInferenceOptions :: InferenceOptions
defaultInferenceOptions = InferenceOptions
  { infOptsVerbosity = Silent
  , infOptsPrintGraphs = False
  , infOptsMode = InferNominal 
  , infOptsSimplify = True 
  , infOptsLibPath = []
  }


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

guardPrintGraphs :: IO () -> DriverM ()
guardPrintGraphs action = do
  printGraphs <- gets (infOptsPrintGraphs . driverOpts)
  when printGraphs (liftIO action)

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
-- Printing TypeAutomata
------------------------------------------------------------------------------

printTrace :: String -> SimplifyTrace pol -> IO ()
printTrace str trace = do
  printGraph ("0_typeAut_"       <> str) (trace_typeAut        trace)
  printGraph ("1_typeAutDet"     <> str) (trace_typeAutDet     trace)
  printGraph ("2_typeAutDetAdms" <> str) (trace_typeAutDetAdms trace)
  printGraph ("3_minTypeAut"     <> str) (trace_minTypeAut     trace)

printGraph :: String -> TypeAut' EdgeLabelNormal f pol -> IO ()
printGraph fileName aut = do
  let graphDir = "graphs"
  let fileUri = "  file://"
  let jpg = "jpg"
  let xdot = "xdot"
  dotInstalled <- isGraphvizInstalled
  if dotInstalled
    then do
      createDirectoryIfMissing True graphDir
      currentDir <- getCurrentDirectory
      _ <- runGraphviz (typeAutToDot aut) Jpeg           (graphDir </> fileName <.> jpg)
      _ <- runGraphviz (typeAutToDot aut) (XDot Nothing) (graphDir </> fileName <.> xdot)
      putStrLn (fileUri ++ currentDir </> graphDir </> fileName <.> jpg)
    else do
      putStrLn "Cannot generate graphs: graphviz executable not found in path."


---------------------------------------------------------------------------------
-- Infer Declarations
---------------------------------------------------------------------------------

inferDecl :: Declaration Parsed
           -> DriverM (Declaration Inferred)
--
-- PrdCnsDecl
--
inferDecl (PrdCnsDecl loc pc isRec fv annot term) = do
  infopts <- gets driverOpts
  env <- gets driverEnv
  -- 1. Generate the constraints.
  let genFun = case isRec of
        Recursive -> genConstraintsTermRecursive loc fv pc term
        NonRecursive -> genConstraintsTerm term
  (tmInferred, constraintSet) <- liftEitherErr loc $ runGenM env (infOptsMode infopts) genFun
  guardVerbose $ ppPrintIO constraintSet
  -- 2. Solve the constraints.
  solverResult <- liftEitherErr loc $ solveConstraints constraintSet env (infOptsMode infopts)
  guardVerbose $ ppPrintIO solverResult
  -- 3. Coalesce the result
  let bisubst = coalesce solverResult
  guardVerbose $ ppPrintIO bisubst
  -- 4. Read of the type and generate the resulting type
  let typ = zonkType bisubst (getTypeTerm tmInferred)
  guardVerbose $ putStr "\nInferred type: " >> ppPrintIO typ >> putStrLn ""
  -- 5. Simplify
  typSimplified <- case infOptsSimplify infopts of
    True -> do
      (simpTrace, tys) <- liftEitherErr loc $ simplify (generalize typ)
      guardPrintGraphs $ printTrace (T.unpack fv) simpTrace
      guardVerbose $ putStr "\nInferred type (Simplified): " >> ppPrintIO tys >> putStrLn ""
      return tys
    False -> return (generalize typ)
  -- 6. Check type annotation.
  ty <- checkAnnot typSimplified annot loc
  -- 7. Insert into environment
  env <- gets driverEnv
  case pc of
    PrdRep -> do
      let newEnv = env { prdEnv  = M.insert fv (tmInferred ,loc, ty) (prdEnv env) }
      setEnvironment newEnv
      return (PrdCnsDecl loc pc isRec fv (Just ty) tmInferred)
    CnsRep -> do
      let newEnv = env { cnsEnv  = M.insert fv (tmInferred, loc, ty) (cnsEnv env) }
      setEnvironment newEnv
      return (PrdCnsDecl loc pc isRec fv (Just ty) tmInferred)
--
-- CmdDecl
--
inferDecl (CmdDecl loc v cmd) = do
  infopts <- gets driverOpts
  env <- gets driverEnv
  -- Generate the constraints
  (cmdInferred,constraints) <- liftEitherErr loc $ runGenM env (infOptsMode infopts) (genConstraintsCommand cmd)
  -- Solve the constraints
  solverResult <- liftEitherErr loc $ solveConstraints constraints env (infOptsMode infopts)
  guardVerbose $ do
      ppPrintIO constraints
      ppPrintIO solverResult
  -- Insert into environment
  env <- gets driverEnv
  let newEnv = env { cmdEnv  = M.insert v (cmdInferred, loc) (cmdEnv env)}
  setEnvironment newEnv
  return (CmdDecl loc v cmdInferred)
--
-- DataDecl
--
inferDecl (DataDecl loc dcl) = do
  -- Insert into environment
  -- TODO: Check data decls
  env <- gets driverEnv
  let newEnv = env { declEnv = (loc,dcl) : declEnv env}
  setEnvironment newEnv
  return (DataDecl loc dcl)
--
-- ImportDecl
--
inferDecl (ImportDecl loc mod) = do
  fp <- findModule mod loc
  oldEnv <- gets driverEnv
  newEnv <- fst <$> inferProgramFromDisk fp
  setEnvironment (oldEnv <> newEnv)
  return (ImportDecl loc mod)
--
-- SetDecl
--
inferDecl (SetDecl loc txt) = case T.unpack txt of
  "refined" -> do
    modify (\DriverState { driverOpts, driverEnv} -> DriverState driverOpts { infOptsMode = InferRefined }driverEnv)
    return (SetDecl loc txt)
  _ -> throwError (Located loc (OtherError ("Unknown option: " <> txt)))
--
-- ParseErrorDecl
--
inferDecl ParseErrorDecl = do
    throwError (Located defaultLoc (OtherError "Should not occur: Tried to insert ParseErrorDecl into Environment"))

---------------------------------------------------------------------------------
-- Infer programs
---------------------------------------------------------------------------------

inferProgramFromDisk :: FilePath
                     -> DriverM (Environment, Program Inferred)
inferProgramFromDisk fp = do
  file <- liftIO $ T.readFile fp
  let parsed = runFileParser fp programP file
  case parsed of
    Left err -> throwError (Located defaultLoc (OtherError (T.pack (errorBundlePretty err))))
    Right decls -> do
        -- Use inference options of parent? Probably not?
        x <- liftIO $ inferProgramIO  (DriverState defaultInferenceOptions { infOptsLibPath = ["examples"] } mempty) decls
        case x of
            Left err -> throwError err
            Right env -> return env

inferProgram :: [Declaration Parsed]
             -> DriverM (Program Inferred)
inferProgram decls = forM decls inferDecl



inferProgramIO  :: DriverState -- ^ Initial State
                -> [Declaration Parsed]
                -> IO (Either LocatedError (Environment, Program Inferred))
inferProgramIO state decls = do
    x <- execDriverM state (inferProgram decls)
    case x of
        Left err -> return (Left err)
        Right (res,x) -> return (Right ((driverEnv x), res))
