module Driver.Definition where

import Control.Monad.Except
import Control.Monad.State
import Data.List (find)
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
  { infOptsVerbosity   :: Verbosity      -- ^ Whether to print debug information to the terminal.
  , infOptsPrintGraphs :: Bool           -- ^ Whether to print graphs from type simplification.
  , infOptsSimplify    :: Bool           -- ^ Whether or not to simplify types.
  , infOptsLibPath     :: [FilePath]     -- ^ Where to search for imported modules.
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
  { driverOpts :: InferenceOptions
  , driverEnv :: Environment
  , driverSymbols :: [(ModuleName, SymbolTable)]
  , driverASTs :: [(ModuleName, AST.Program)]
  }

defaultDriverState :: DriverState
defaultDriverState = MkDriverState
  { driverOpts = defaultInferenceOptions { infOptsLibPath = ["examples"] }
  , driverEnv = mempty
  , driverSymbols = []
  , driverASTs = []
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
    f state@MkDriverState { driverSymbols } = state { driverSymbols = (mn,st) : driverSymbols }

getSymbolTables :: DriverM [(ModuleName, SymbolTable)]
getSymbolTables = gets driverSymbols


-- AST Cache

addTypecheckedProgram :: ModuleName -> AST.Program -> DriverM ()
addTypecheckedProgram mn prog = modify f
  where
    f state@MkDriverState { driverASTs } = state { driverASTs = (mn,prog) : driverASTs }

queryTypecheckedProgram :: ModuleName -> DriverM (AST.Program)
queryTypecheckedProgram mn = do
  cache <- gets driverASTs
  case find (\(mn',ast) -> mn == mn') cache of
    Nothing -> throwOtherError ["Module " <> ppPrint mn <> " not in cache."]
    Just (_,ast) -> pure ast


-- Environment

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

liftErr :: Loc -> Error -> DriverM a
liftErr loc err = do
    let locerr = attachLoc loc err
    guardVerbose $ printLocatedError locerr
    throwError locerr

liftEitherErr :: Loc -> Either Error a -> DriverM a
liftEitherErr loc x = case x of
    Left err -> liftErr loc err
    Right res -> return res
