module Renamer.Definition where

import Control.Monad.Except (throwError)
import Control.Monad.State
import Data.Map qualified as M
import Data.Text qualified as T
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist )

import Driver.Definition
import Driver.Environment
import Pretty.Pretty
import Syntax.Common
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
    Nothing -> throwError $ OtherError (Just loc) ((case dc of Data -> "Constructor"; Codata -> "Destructor") <>" not in symbol table: " <> ppPrint xtor)
    Just ns -> pure ns

-- | Find the Arity of a given typename
lookupTypeConstructorAritiy :: TypeName -> RenamerM (PolyKind)
lookupTypeConstructorAritiy tn = do
    symbolTable <- getSymbolTable
    case M.lookup tn (tyConMap symbolTable) of
        Just (_,polykind) -> pure polykind
        Nothing -> throwOtherError ["Type name " <> unTypeName tn <> " not found in symbol table"]

------------------------------------------------------------------------------
-- Deprecated stuff
------------------------------------------------------------------------------

updateSymbolTable :: (SymbolTable -> SymbolTable) -> RenamerM ()
updateSymbolTable f = do
    env <- gets driverEnv
    let newEnv = env { symbolTable = f (symbolTable env)}
    modify (\state -> state { driverEnv = newEnv })


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
createSymbolTable ((CST.DataDecl _ CST.NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors }):decls) =
  -- Create the default polykind
  let polyKind = case data_kind of
                    Nothing -> MkPolyKind [] [] (case data_polarity of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
      ns = case data_refined of
               Refined -> Refinement
               NotRefined -> Nominal
      st = createSymbolTable decls
      xtors = M.fromList [((CST.sig_name xt, data_polarity), (ns, CST.linearContextToArity (CST.sig_args xt)))| xt <- data_xtors]
  in st { xtorMap  = M.union xtors (xtorMap st)
        , tyConMap = M.insert data_name (data_refined, polyKind)(tyConMap st)}
createSymbolTable (_:decls) = createSymbolTable decls


