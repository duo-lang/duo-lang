module Renamer.Definition where

import Control.Monad.Except (throwError)
import Control.Monad.State
import Data.Map qualified as M
import Data.Text qualified as T
import Data.List (find)
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist )

import Driver.Definition
import Driver.Environment
import Pretty.Pretty
import Syntax.Common
import qualified Syntax.AST.Types as AST
import qualified Syntax.CST.Program as CST
import qualified Syntax.CST.Types as CST
import Utils
import Errors

------------------------------------------------------------------------------
-- Renamer Monad
------------------------------------------------------------------------------

type RenamerM a = DriverM a

------------------------------------------------------------------------------
-- Helper Functions
------------------------------------------------------------------------------

getSymbolTable :: RenamerM SymbolTable
getSymbolTable = gets (symbolTable . driverEnv)


lookupXtor :: Loc -> (XtorName, DataCodata) -> RenamerM (NominalStructural, Arity)
lookupXtor loc xs@(xtor,dc) = do
  symbolTable <- getSymbolTable
  case M.lookup xs (xtorMap symbolTable) of
    Nothing -> throwError $ OtherError (Just loc) ((case dc of Data -> "Constructor"; Codata -> "Destructor") <>" not in environment: " <> ppPrint xtor)
    Just ns -> pure ns

-- | Find the number of (contravariant, covariant) type parameters
lookupTypeConstructorAritiy :: TypeName -> RenamerM (Int, Int)
lookupTypeConstructorAritiy tn = do
    MkEnvironment {..} <- gets driverEnv
    let env = snd <$> declEnv
    case find (\AST.NominalDecl{..} -> data_name == tn) env of
        Just AST.NominalDecl{..} -> pure (length (contravariant data_kind), length (covariant data_kind))
        Nothing -> throwOtherError ["Type name " <> unTypeName tn <> " not found in environment"]


------------------------------------------------------------------------------
-- Deprecated stuff
------------------------------------------------------------------------------

updateSymbolTable :: (SymbolTable -> SymbolTable) -> RenamerM ()
updateSymbolTable f = do
    env <- getDriverEnv
    let newEnv = env { symbolTable = f (symbolTable env)}
    modify (\state -> state { driverEnv = newEnv })

getDriverEnv :: RenamerM (Environment Inferred)
getDriverEnv = gets driverEnv

setEnvironment :: Environment Inferred -> RenamerM ()
setEnvironment env = modify (\state -> state { driverEnv = env })

-- | Given the Library Paths contained in the inference options and a module name,
-- try to find a filepath which corresponds to the given module name.
findModule :: ModuleName -> Loc ->  RenamerM FilePath
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


createSymbolTable :: CST.Program  -> SymbolTable
createSymbolTable [] = mempty
createSymbolTable ((CST.XtorDecl _ dc xt args _):decls) =
  let st = createSymbolTable decls
  in st { xtorMap = M.insert (xt,dc) (Structural, fst <$> args) (xtorMap st)}
createSymbolTable ((CST.DataDecl _ dd):decls) =
  let ns = case CST.data_refined dd of
               Refined -> Refinement
               NotRefined -> Nominal
      st = createSymbolTable decls
      xtors = M.fromList [((CST.sig_name xt, CST.data_polarity dd), (ns, CST.linearContextToArity (CST.sig_args xt)))| xt <- CST.data_xtors dd]
  in st { xtorMap  = M.union xtors (xtorMap st) }
createSymbolTable (_:decls) = createSymbolTable decls


