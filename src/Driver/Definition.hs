module Driver.Definition where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Text qualified as T
import Data.Map (Map)
import Data.Map qualified as M
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist )

import Errors
import Pretty.Errors ( printLocatedError )
import Syntax.AST.Program qualified as AST
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.AST.Types (IsRefined(..))
import Syntax.CommonTerm
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
-- Symbol Table
---------------------------------------------------------------------------------

type SymbolTable = Map XtorName' IsRefined

emptySymbolTable :: SymbolTable
emptySymbolTable = M.empty

createSymbolTable :: CST.Program -> SymbolTable
createSymbolTable decls = go decls M.empty
  where
    go [] acc = acc
    go (decl:decls) acc = go decls (addDecl decl acc)

addDecl :: CST.Declaration -> SymbolTable -> SymbolTable
addDecl (CST.DataDecl _loc CST.NominalDecl { data_refined, data_xtors }) m =
    let
        xtors = CST.sig_name <$> data_xtors
        newm = M.fromList [(xtor, data_refined) | xtor <- xtors]
    in
      M.union m newm
addDecl _ m = m


---------------------------------------------------------------------------------
-- Driver Monad
---------------------------------------------------------------------------------

type DriverReader = SymbolTable

data DriverState = DriverState
  { driverOpts :: InferenceOptions
  , driverEnv :: AST.Environment Inferred
  }

newtype DriverM a = DriverM { unDriverM :: ReaderT DriverReader (StateT DriverState  (ExceptT Error IO)) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadState DriverState, MonadIO, MonadReader DriverReader)

execDriverM :: DriverReader
            -> DriverState 
            ->  DriverM a
            -> IO (Either Error (a,DriverState))
execDriverM reader state act = runExceptT $ runStateT (runReaderT (unDriverM act) reader) state

---------------------------------------------------------------------------------
-- Utility functions
---------------------------------------------------------------------------------

setEnvironment :: AST.Environment Inferred -> DriverM ()
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

lowerXtorName :: Bool -> XtorName' -> DriverM XtorName
lowerXtorName True (MkXtorName' xt) = pure (MkXtorName Structural xt)
lowerXtorName False xtor@(MkXtorName' xt) = do
    st <- ask
    case M.lookup xtor st of
        Nothing -> throwError (OtherError Nothing (T.pack ("The symbol" <> show xt <> " is not in symbol table: " <> show (M.toList st))))
        Just Refined -> pure (MkXtorName Refinement xt)
        Just NotRefined -> pure (MkXtorName Nominal xt)
