module Driver.Definition where

import Control.Monad.Except
import Control.Monad.State
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist )


import Driver.Environment ( Environment, emptyEnvironment )
import Errors
import Pretty.Pretty
import Pretty.Errors ( printLocatedError )
import Renamer.SymbolTable
import Syntax.Common.Names ( ModuleName(MkModuleName) )
import Syntax.TST.Program qualified as TST
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
-- Driver State
---------------------------------------------------------------------------------

-- | The state of the driver during compilation.
data DriverState = MkDriverState
  { drvOpts    :: InferenceOptions
    -- ^ The inference options
  , drvEnv     :: Map ModuleName Environment
  , drvFiles   :: Map ModuleName FilePath
  , drvSymbols :: Map ModuleName SymbolTable
  , drvASTs    :: Map ModuleName TST.Program
  }

defaultDriverState :: DriverState
defaultDriverState = MkDriverState
  { drvOpts = defaultInferenceOptions { infOptsLibPath = ["examples"] }
  , drvEnv = M.empty
  , drvFiles = M.empty
  , drvSymbols = M.empty
  , drvASTs = M.empty
  }

---------------------------------------------------------------------------------
-- Driver Monad
---------------------------------------------------------------------------------

newtype DriverM a = DriverM { unDriverM :: StateT DriverState  (ExceptT Error IO) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadState DriverState, MonadIO)

instance MonadFail DriverM where
  fail str = throwError (OtherError Nothing (T.pack str))
  
execDriverM :: DriverState ->  DriverM a -> IO (Either Error (a,DriverState))
execDriverM state act = runExceptT $ runStateT (unDriverM act) state

---------------------------------------------------------------------------------
-- Utility functions
---------------------------------------------------------------------------------

-- Symbol tables

addSymboltable :: ModuleName -> SymbolTable -> DriverM ()
addSymboltable mn st = modify f
  where
    f state@MkDriverState { drvSymbols } = state { drvSymbols = M.insert mn st drvSymbols }

getSymbolTables :: DriverM (Map ModuleName SymbolTable)
getSymbolTables = gets drvSymbols


-- AST Cache

addTypecheckedProgram :: ModuleName -> TST.Program -> DriverM ()
addTypecheckedProgram mn prog = modify f
  where
    f state@MkDriverState { drvASTs } = state { drvASTs = M.insert mn prog  drvASTs }

queryTypecheckedProgram :: ModuleName -> DriverM TST.Program
queryTypecheckedProgram mn = do
  cache <- gets drvASTs
  case M.lookup mn cache of
    Nothing -> throwOtherError [ "AST for module " <> ppPrint mn <> " not in cache."
                               , "Available ASTs: " <> ppPrint (M.keys cache)
                               ]
    Just ast -> pure ast


-- Environment

modifyEnvironment :: ModuleName -> (Environment -> Environment) -> DriverM ()
modifyEnvironment mn f = do
  env <- gets drvEnv
  case M.lookup mn env of
    Nothing -> do
      let newEnv = M.insert mn (f emptyEnvironment) env
      modify (\state -> state { drvEnv = newEnv })
    Just en -> do
      let newEnv = M.insert mn (f en) env
      modify (\state -> state { drvEnv = newEnv })

-- | Only execute an action if verbosity is set to Verbose.
guardVerbose :: IO () -> DriverM ()
guardVerbose action = do
    verbosity <- gets (infOptsVerbosity . drvOpts)
    when (verbosity == Verbose) (liftIO action)

-- | Given the Library Paths contained in the inference options and a module name,
-- try to find a filepath which corresponds to the given module name.
findModule :: ModuleName -> Loc ->  DriverM FilePath
findModule (MkModuleName mod) loc = do
  infopts <- gets drvOpts
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
