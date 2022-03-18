module Driver.Definition where

import Control.Monad.Except
import Control.Monad.State
import Control.Monad.Reader
import Data.Text qualified as T
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist )

import Driver.SymbolTable
import Errors
import Pretty.Errors ( printLocatedError )
import Syntax.Environment
import Syntax.Common
import Utils

------------------------------------------------------------------------------
-- Typeinference Options
------------------------------------------------------------------------------

data InferenceOptions = InferenceOptions
  { infOptsVerbosity   :: Verbosity      -- ^ Whether to print debug information to the terminal.
  , infOptsPrintGraphs :: Bool           -- ^ Whether to print graphs from type simplification.
  , infOptsSimplify    :: Bool           -- ^ Whether or not to simplify types.
  , infOptsLibPath     :: [FilePath]     -- ^ Where to search for imported modules.
  } deriving (Show)

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

data DriverState = DriverState
  { driverOpts :: InferenceOptions
  , driverEnv :: Environment Inferred
  } deriving (Show)

newtype DriverM a = DriverM { unDriverM :: ReaderT SymbolTable (StateT DriverState  (ExceptT Error IO)) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadState DriverState, MonadIO, MonadReader SymbolTable)

execDriverM :: DriverState -> SymbolTable -> DriverM a -> IO (Either Error (a,DriverState))
execDriverM state symbolTable action =
  runExceptT $ runStateT (runReaderT (unDriverM action) symbolTable) state

---------------------------------------------------------------------------------
-- Utility functions
---------------------------------------------------------------------------------

setEnvironment :: Environment Inferred -> DriverM ()
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
