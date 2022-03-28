module Renamer.Definition where

import Control.Monad.Except (throwError)
import Control.Monad.State
import Data.Map (Map)
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
import Utils
import Errors

------------------------------------------------------------------------------
-- Symbol Table
------------------------------------------------------------------------------

type SymbolTable = Map (XtorName, DataCodata) (NominalStructural, Arity)

------------------------------------------------------------------------------
-- Renamer Monad
------------------------------------------------------------------------------

type RenamerM a = DriverM a

------------------------------------------------------------------------------
-- Helper Functions
------------------------------------------------------------------------------

getSymbolTable :: RenamerM SymbolTable
getSymbolTable = gets (xtorMap . driverEnv)


lookupXtor :: Loc -> (XtorName, DataCodata) -> RenamerM (NominalStructural, Arity)
lookupXtor loc xs@(xtor,dc) = do
  xtorMap <- getSymbolTable
  case M.lookup xs xtorMap of
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