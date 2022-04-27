module Driver.Definition where

import Control.Monad.Except
import Control.Monad.State
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist )


import Driver.Environment
import Errors
import Pretty.Pretty
import Pretty.Errors ( printLocatedError )
import Renamer.SymbolTable
import Syntax.Common
import Syntax.AST.Program qualified as AST
import Utils

------------------------------------------------------------------------------
-- Typeinference Options
------------------------------------------------------------------------------

data InferenceOptions = InferenceOptions
  { infOptsVerbosity   :: Verbosity
    -- ^ Whether to print debug information to the terminal.
  , infOptsPrintGraphs :: Bool
    -- ^ Whether to print graphs from type simplification.
  , infOptsSimplify    :: Bool
    -- ^ Whether or not to simplify types.
  , infOptsLibPath     :: [FilePath]
    -- ^ Where to search for imported modules.
  }

defaultInferenceOptions :: InferenceOptions
defaultInferenceOptions = InferenceOptions
  { infOptsVerbosity = Silent
  , infOptsPrintGraphs = False
  , infOptsSimplify = True
  , infOptsLibPath = []
  }

---------------------------------------------------------------------------------
-- Driver Monad
---------------------------------------------------------------------------------

data DriverState = MkDriverState
  { driverOpts    :: InferenceOptions
  , driverEnv     :: Map ModuleName Environment
  , driverSymbols :: Map ModuleName SymbolTable
  , driverASTs    :: Map ModuleName AST.Program
  }

defaultDriverState :: DriverState
defaultDriverState = MkDriverState
  { driverOpts = defaultInferenceOptions { infOptsLibPath = ["examples"] }
  , driverEnv = M.empty
  , driverSymbols = M.empty
  , driverASTs = M.empty
  }

newtype DriverM a = DriverM { unDriverM :: StateT DriverState  (ExceptT Error IO) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadState DriverState, MonadIO)

execDriverM :: DriverState ->  DriverM a -> IO (Either Error (a,DriverState))
execDriverM state act = runExceptT $ runStateT (unDriverM act) state

---------------------------------------------------------------------------------
-- Utility functions
---------------------------------------------------------------------------------

-- Symbol tables

addSymboltable :: ModuleName -> SymbolTable -> DriverM ()
addSymboltable mn st = modify f
  where
    f state@MkDriverState { driverSymbols } = state { driverSymbols = M.insert mn st driverSymbols }

getSymbolTables :: DriverM (Map ModuleName SymbolTable)
getSymbolTables = gets driverSymbols


-- AST Cache

addTypecheckedProgram :: ModuleName -> AST.Program -> DriverM ()
addTypecheckedProgram mn prog = modify f
  where
    f state@MkDriverState { driverASTs } = state { driverASTs = M.insert mn prog  driverASTs }

queryTypecheckedProgram :: ModuleName -> DriverM AST.Program
queryTypecheckedProgram mn = do
  cache <- gets driverASTs
  case M.lookup mn cache of
    Nothing -> throwOtherError [ "AST for module " <> ppPrint mn <> " not in cache."
                               , "Available ASTs: " <> ppPrint (M.keys cache)
                               ]
    Just ast -> pure ast


-- Environment

modifyEnvironment :: ModuleName -> (Environment -> Environment) -> DriverM ()
modifyEnvironment mn f = do
  env <- gets driverEnv
  case M.lookup mn env of
    Nothing -> do
      let newEnv = M.insert mn (f (MkEnvironment M.empty M.empty M.empty [])) env
      modify (\state -> state { driverEnv = newEnv })
    Just en -> do
      let newEnv = M.insert mn (f en) env
      modify (\state -> state { driverEnv = newEnv })

-- | Only execute an action if verbosity is set to Verbose.
guardVerbose :: IO () -> DriverM ()
guardVerbose action = do
    verbosity <- gets (infOptsVerbosity . driverOpts)
    when (verbosity == Verbose) (liftIO action)

-- | Given the Library Paths contained in the inference options and a module name,
-- try to find a filepath which corresponds to the given module name.
findModule :: ModuleName -> Loc ->  DriverM FilePath
findModule (MkModuleName mod) loc = do
  infopts <- gets driverOpts
  let libpaths = infOptsLibPath infopts
  fps <- forM libpaths $ \libpath -> do
    let fp = libpath </> T.unpack mod <.> "ds"
    exists <- liftIO $ doesFileExist fp
    if exists then return [fp] else return []
  case concat fps of
    [] -> throwError $ OtherError (Just loc) ("Could not locate library: " <> mod)
    (fp:_) -> return fp

liftErr :: Error -> DriverM a
liftErr err = do
    guardVerbose $ printLocatedError err
    throwError err

liftErrLoc :: Loc -> Error -> DriverM a
liftErrLoc loc err = do
    let locerr = attachLoc loc err
    guardVerbose $ printLocatedError locerr
    throwError locerr

liftEitherErr :: Either Error a -> DriverM a
liftEitherErr x = case x of
    Left err -> liftErr err
    Right res -> return res

liftEitherErrLoc :: Loc -> Either Error a -> DriverM a
liftEitherErrLoc loc x = case x of
    Left err -> liftErrLoc loc err
    Right res -> return res
