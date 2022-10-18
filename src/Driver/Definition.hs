module Driver.Definition where

import Control.Monad.Except
import Control.Monad.State
import Data.Map (Map)
import Data.Map qualified as M
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Text qualified as T
import System.Directory ( makeAbsolute )


import Driver.Environment ( Environment, emptyEnvironment )
import Errors
import Pretty.Pretty
import Pretty.Errors ( printLocatedReport )
import Resolution.SymbolTable
import Syntax.CST.Names ( ModuleName(..) )
import Syntax.TST.Program qualified as TST
import Loc
import Utils
import Control.Monad.Writer
import qualified Syntax.CST.Program as CST (Module(..))
import qualified Data.Text.IO as T
import Parser.Definition (runFileParser)
import Parser.Parser (moduleP)
import Data.Maybe ( fromMaybe, catMaybes )
import TypeAutomata.Definition (Nubable(nub))

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
  , infOptsLibPath = [".", "std", "examples"]
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
  , drvFiles   :: !(Map ModuleName CST.Module)
  , drvSymbols :: !(Map ModuleName SymbolTable)
  , drvASTs    :: Map ModuleName TST.Module
  , drvErrs    :: Map ModuleName [Error]
  }

defaultDriverState :: DriverState
defaultDriverState = MkDriverState
  { drvOpts = defaultInferenceOptions
  , drvEnv = M.empty
  , drvFiles = M.empty
  , drvSymbols = M.empty
  , drvASTs = M.empty
  , drvErrs = M.empty
  }

---------------------------------------------------------------------------------
-- Driver Monad
---------------------------------------------------------------------------------

newtype DriverM a = DriverM { unDriverM :: (StateT DriverState  (ExceptT (NonEmpty Error) (WriterT [Warning] IO))) a }
  deriving newtype (Functor, Applicative, Monad, MonadError (NonEmpty Error), MonadState DriverState, MonadIO, MonadWriter [Warning])

instance MonadFail DriverM where
  fail str = throwOtherError defaultLoc [T.pack str]

execDriverM :: DriverState ->  DriverM a -> IO (Either (NonEmpty Error) (a,DriverState),[Warning])
execDriverM state act = runWriterT $ runExceptT $ runStateT (unDriverM act) state

---------------------------------------------------------------------------------
-- Utility functions
---------------------------------------------------------------------------------

-- Error list

getModuleErrors :: DriverState -> ModuleName -> [Error]
getModuleErrors ds mn = fromMaybe [] $ M.lookup mn $ drvErrs ds

getModuleErrorsTrans :: DriverState -> ModuleName -> [Error]
getModuleErrorsTrans ds mn = concatMap (fromMaybe [] . flip M.lookup (drvErrs ds)) (mn:mns)
  where
  mns :: [ModuleName]
  mns = getDependencies ds mn

getErrors :: DriverState -> [Error]
getErrors ds = concat $ M.elems $ drvErrs ds

addErrors :: ModuleName -> [Error] -> DriverM ()
addErrors mn errs = modify (\ds -> ds { drvErrs = mapAppend mn errs $ drvErrs ds } )

addErrorsNonEmpty :: ModuleName -> a -> NonEmpty Error -> DriverM a
addErrorsNonEmpty mn a (e :| es) = addErrors mn (e : es) >> return a

-- Symbol tables

addSymboltable :: ModuleName -> SymbolTable -> DriverM ()
addSymboltable mn st = modify f
  where
    f state@MkDriverState { drvSymbols } = state { drvSymbols = M.insert mn st drvSymbols }

getSymbolTables :: DriverM (Map ModuleName SymbolTable)
getSymbolTables = gets drvSymbols

getSymbolTable  :: CST.Module
                -> DriverM SymbolTable
getSymbolTable mod = do
  sts <- getSymbolTables
  case M.lookup (CST.mod_name mod) sts of
    Nothing -> do
      st <- createSymbolTable mod
      addSymboltable (CST.mod_name mod) st
      return st
    Just st -> return st

getImports :: ModuleName -> DriverM (Maybe [ModuleName])
getImports mn = gets $ fmap (fmap fst . imports) . M.lookup mn . drvSymbols

getDependencies :: DriverState -> ModuleName -> [ModuleName]
getDependencies ds mn = nub $ directDeps ++ concatMap (getDependencies ds) directDeps
  where
    directDeps = maybe [] (fmap fst . imports) . M.lookup mn . drvSymbols $ ds


-- Modules and declarations

checkModuleName :: MonadError (NonEmpty Error) m => ModuleName -> CST.Module -> m ()
checkModuleName mn CST.MkModule { mod_name } =
  if mn == mod_name
    then pure ()
    else throwOtherError defaultLoc [ "Wrong module declaration: Found declaration " <> T.pack (ppPrintString mod_name) <> " in module " <> T.pack (ppPrintString mn) ]

parseAndCheckModule :: (MonadError (NonEmpty Error) m, MonadIO m) => FilePath -> ModuleName -> FilePath -> m CST.Module
parseAndCheckModule fullFp mn fp = do
  file <- liftIO $ T.readFile fullFp
  mod <- runFileParser fullFp (moduleP fp) file
  checkModuleName mn mod
  pure mod

getModuleDeclarations :: ModuleName -> DriverM CST.Module
getModuleDeclarations mn = do
        moduleMap <- gets drvFiles
        case M.lookup mn moduleMap of
          Just mod -> pure mod
          Nothing -> do
            fp <- findModule mn defaultLoc
            let fullFp = moduleNameToFullPath mn fp
            mod <- parseAndCheckModule fullFp mn fp
            --  file <- liftIO $ T.readFile fullFp
            --  mod <- runFileParser fullFp (moduleP fp) file
            --  checkModuleName mn mod
            addModule mod
            pure mod

addModule :: CST.Module -> DriverM ()
addModule mod = do
  modify (\ds@MkDriverState { drvFiles } -> ds { drvFiles = M.insert (CST.mod_name mod) mod drvFiles })

-- AST Cache

addTypecheckedModule :: ModuleName -> TST.Module -> DriverM ()
addTypecheckedModule mn prog = modify f
  where
    f state@MkDriverState { drvASTs } = state { drvASTs = M.insert mn prog  drvASTs }

queryTypecheckedModule :: ModuleName -> DriverM TST.Module
queryTypecheckedModule mn = do
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
findModule mn@(MkModuleName _path mod) loc = do
  libpaths <- gets $ infOptsLibPath . drvOpts
  isDuoFileMask <- liftIO $ mapM (isModuleFile mn) libpaths
  let duoFiles = catMaybes $ zipWith (\b fp -> if b then Just fp else Nothing) isDuoFileMask libpaths
  case duoFiles of
    [] -> throwOtherError loc $ ["Could not locate library: " <> mod, "Paths searched:"] <> (T.pack <$> libpaths)
    (fp:_fps) -> liftIO $ makeAbsolute fp
      

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
