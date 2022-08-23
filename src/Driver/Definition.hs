module Driver.Definition where

import Control.Monad.Except
import Control.Monad.State
import Data.Map (Map)
import Data.Map qualified as M
import Data.List.NonEmpty (NonEmpty)
import Data.Text qualified as T
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist )


import Driver.Environment ( Environment, emptyEnvironment )
import Errors
import Pretty.Pretty
import Pretty.Errors ( printLocatedReport )
import Resolution.SymbolTable
import Syntax.Common.Names ( ModuleName(MkModuleName) )
import Syntax.TST.Program qualified as TST
import Utils
import Control.Monad.Writer
import Data.Either (rights, lefts)
import qualified Syntax.CST.Program as CST (Program)
import qualified Data.Text.IO as T
import Parser.Definition (runFileParser)
import Parser.Parser (programP)

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
  , infOptsLibPath = [".", "examples"]
  }

setDebugOpts :: InferenceOptions -> InferenceOptions
setDebugOpts infOpts = infOpts { infOptsVerbosity = Verbose }

setPrintGraphOpts :: InferenceOptions -> InferenceOptions
setPrintGraphOpts infOpts = infOpts { infOptsPrintGraphs = True }

---------------------------------------------------------------------------------
-- Driver State
---------------------------------------------------------------------------------

-- | The state of the driver during compilation.
data DriverState = MkDriverState
  { drvOpts    :: InferenceOptions
    -- ^ The inference options
  , drvEnv     :: Map ModuleName Environment
  , drvFiles   :: !(Map ModuleName (FilePath, CST.Program))
  , drvSymbols :: !(Map ModuleName SymbolTable)
  , drvASTs    :: Map ModuleName TST.Program
  }

defaultDriverState :: DriverState
defaultDriverState = MkDriverState
  { drvOpts = defaultInferenceOptions
  , drvEnv = M.empty
  , drvFiles = M.empty
  , drvSymbols = M.empty
  , drvASTs = M.empty
  }

---------------------------------------------------------------------------------
-- Driver Monad
---------------------------------------------------------------------------------

newtype DriverM a = DriverM { unDriverM :: (StateT DriverState  (ExceptT (NonEmpty Error) (WriterT [Warning] IO))) a }
  deriving (Functor, Applicative, Monad, MonadError (NonEmpty Error), MonadState DriverState, MonadIO, MonadWriter [Warning])

instance MonadFail DriverM where
  fail str = throwOtherError defaultLoc [T.pack str]

execDriverM :: DriverState ->  DriverM a -> IO (Either (NonEmpty Error) (a,DriverState),[Warning])
execDriverM state act = runWriterT $ runExceptT $ runStateT (unDriverM act) state

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


-- Modules and declarations

getModuleDeclarations :: ModuleName -> DriverM (FilePath, CST.Program)
getModuleDeclarations mn = do
        moduleMap <- gets drvFiles
        case M.lookup mn moduleMap of
          Just (fp, decls) -> return (fp, decls)
          Nothing -> do
            fp <- findModule mn defaultLoc
            file <- liftIO $ T.readFile fp
            decls <- runFileParser fp programP file
            modify (\ds@MkDriverState { drvFiles } -> ds { drvFiles = M.insert mn (fp, decls) drvFiles })
            return (fp, decls)

-- AST Cache

addTypecheckedProgram :: ModuleName -> TST.Program -> DriverM ()
addTypecheckedProgram mn prog = modify f
  where
    f state@MkDriverState { drvASTs } = state { drvASTs = M.insert mn prog  drvASTs }

queryTypecheckedProgram :: ModuleName -> DriverM TST.Program
queryTypecheckedProgram mn = do
  cache <- gets drvASTs
  case M.lookup mn cache of
    Nothing -> throwOtherError defaultLoc [ "AST for module " <> ppPrint mn <> " not in cache."
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
 --liftIO action
    verbosity <- gets (infOptsVerbosity . drvOpts)
    when (verbosity == Verbose) (liftIO action)

-- | Given the Library Paths contained in the inference options and a module name,
-- try to find a filepath which corresponds to the given module name.
findModule :: ModuleName -> Loc ->  DriverM FilePath
findModule (MkModuleName mod) loc = do
  libpaths <- gets $ infOptsLibPath . drvOpts
  fps <- forM libpaths $ \libpath -> do
    let fp = libpath </> T.unpack mod <.> "duo"
    let fp' = libpath </> T.unpack mod
    exists <- liftIO $ doesFileExist fp
    exists' <- liftIO $ doesFileExist fp'
    let fpRes = if exists then Right fp else Left fp
    let fpRes' = if exists' then Right fp' else Left fp'
    return [fpRes, fpRes']
  let fps' = concat fps
  let hits = rights fps'
  let misses = lefts fps'
  case hits of
    [] -> throwOtherError loc $ ["Could not locate library: " <> mod <> "\n" <> "Paths searched:"] <> fmap T.pack misses
    (fp:_) -> return fp

liftErr :: NonEmpty Error -> DriverM a
liftErr errs = do
    guardVerbose $ do
      forM_ errs $ \err -> printLocatedReport err
    throwError errs

liftErrLoc :: Loc -> NonEmpty Error -> DriverM a
liftErrLoc loc err = do
    let locerr = attachLoc loc <$> err
    guardVerbose $ do
      forM_ locerr $ \err -> printLocatedReport err
    throwError locerr

liftEitherErr :: (Either (NonEmpty Error) a,[Warning]) -> DriverM a
liftEitherErr (x,warnings) = tell warnings >> case x of
    Left err ->  liftErr err
    Right res -> return res

liftEitherErrLoc :: Loc -> Either (NonEmpty Error) a -> DriverM a
liftEitherErrLoc loc x = case x of
    Left err -> liftErrLoc loc err
    Right res -> return res
