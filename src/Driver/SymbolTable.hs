module Driver.SymbolTable where

import Control.Monad.IO.Class
import Control.Monad.Except
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Map (Map)
import Data.Map qualified as M
import Text.Megaparsec ( errorBundlePretty )

import Errors
import Parser.Parser ( runFileParser, programP )
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.Common
import Syntax.Kinds


---------------------------------------------------------------------------------
-- SymbolTable
--
-- The symbol table contains all the information we can get from a CST.Program
-- without having to lower any of the declarations contained in the program.
--
---------------------------------------------------------------------------------

data SymbolTable = MkSymbolTable {
     xtorMap :: Map (XtorName,DataCodata) (NominalStructural, Arity),
     tyConMap :: Map TypeName (IsRefined, DataCodata, TParams, Kind)
}

instance Semigroup SymbolTable where
  (MkSymbolTable m1 m2) <> (MkSymbolTable m1' m2') =
    MkSymbolTable (M.union m1 m1') (M.union m2 m2')

instance Monoid SymbolTable where
  mempty = MkSymbolTable M.empty M.empty

---------------------------------------------------------------------------------
-- Creating a SymbolTable
---------------------------------------------------------------------------------

createSymbolTable :: CST.Program  -> SymbolTable
createSymbolTable [] = mempty
createSymbolTable ((CST.XtorDecl _ dc xt args _):decls) =
  let st = createSymbolTable decls
  in MkSymbolTable (M.insert (xt,dc) (Structural, fst <$> args) (xtorMap st)) (tyConMap st)
createSymbolTable ((CST.DataDecl _ dd):decls) =
  let ns = case CST.data_refined dd of
               Refined -> Refinement
               NotRefined -> Nominal
      st = createSymbolTable decls
      xtors = M.fromList [((CST.sig_name xt, CST.data_polarity dd), (ns, CST.linearContextToArity (CST.sig_args xt)))| xt <- CST.data_xtors dd]
  in MkSymbolTable (M.union xtors (xtorMap st)) (tyConMap st)
createSymbolTable (_:decls) = createSymbolTable decls


createSymbolTableFromDisk :: (MonadIO m, MonadError Error m) => FilePath
                          -> m SymbolTable
createSymbolTableFromDisk fp = do
  file <- liftIO $ T.readFile fp
  let parsed = runFileParser fp programP file
  case parsed of
    Left err -> throwOtherError [T.pack (errorBundlePretty err)]
    Right decls -> pure $ createSymbolTable decls