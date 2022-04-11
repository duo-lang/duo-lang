module Renamer.Definition where

import Control.Monad.Except (throwError)
import Control.Monad.State
import Data.Map qualified as M
import Data.Text qualified as T
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist )

import Driver.Definition
import Pretty.Pretty
import Renamer.SymbolTable
import Syntax.Common
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
getSymbolTable = gets driverSymbols


lookupXtor :: Loc -> (XtorName, DataCodata) -> RenamerM (NominalStructural, Arity)
lookupXtor loc xs@(xtor,dc) = do
  symbolTable <- getSymbolTable
  case M.lookup xs (xtorMap symbolTable) of
    Nothing -> throwError $ OtherError (Just loc) ((case dc of Data -> "Constructor"; Codata -> "Destructor") <>" not in symbol table: " <> ppPrint xtor)
    Just ns -> pure ns

-- | Find the Arity of a given typename
lookupTypeConstructor :: Loc -> TypeName -> RenamerM TyConResult
lookupTypeConstructor loc tn = do
    symbolTable <- getSymbolTable
    case M.lookup tn (tyConMap symbolTable) of
        Just res -> pure res
        Nothing -> throwError (OtherError (Just loc) ("Type name " <> unTypeName tn <> " not found in symbol table"))

------------------------------------------------------------------------------
-- Deprecated stuff
------------------------------------------------------------------------------

updateSymbolTable :: (SymbolTable -> SymbolTable) -> RenamerM ()
updateSymbolTable f = do
    symbolTable <- gets driverSymbols
    let newSymbolTable = f symbolTable
    modify (\state -> state { driverSymbols = newSymbolTable })


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



