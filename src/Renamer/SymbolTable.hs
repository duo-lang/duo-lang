module Renamer.SymbolTable where

import Control.Monad.Except
import Data.Map (Map)
import Data.Map qualified as M

import Errors
import Syntax.Common
import Syntax.CST.Program
import Syntax.CST.Types
import Utils

---------------------------------------------------------------------------------
-- Type Operators
---------------------------------------------------------------------------------

data TyOpDesugaring where
    UnionDesugaring :: TyOpDesugaring
    InterDesugaring :: TyOpDesugaring
    NominalDesugaring :: TypeName -> TyOpDesugaring

data TyOp = MkTyOp
    {
        symbol :: BinOp,
        prec :: Precedence,
        assoc :: Associativity,
        desugar :: TyOpDesugaring
    }

---------------------------------------------------------------------------------
-- Symbol Table
---------------------------------------------------------------------------------

-- | What a TypeName can resolve to during name resolution
data TypeNameResolve where
  -- | Typename was introduced in a data or codata declaration
  NominalResult :: DataCodata -> IsRefined -> PolyKind -> TypeNameResolve
  -- | TypeName was introduced in a type synonym
  SynonymResult :: Typ -> TypeNameResolve

-- | What a XtorName can resolve to during name resolution
data XtorNameResolve where
  -- | Xtor was introduced in a data or codata declaration
  XtorNameResult :: DataCodata ->  NominalStructural -> Arity -> XtorNameResolve

-- | What a toplevel definition can resolve to during name resolution
data FreeVarNameResolve where
  FreeVarResult :: FreeVarNameResolve

data SymbolTable = MkSymbolTable
  { xtorNameMap :: Map XtorName    XtorNameResolve
  , typeNameMap :: Map TypeName    TypeNameResolve
  , freeVarMap  :: Map FreeVarName FreeVarNameResolve
  , tyOps :: [TyOp]
  , imports :: [(ModuleName, Loc)]
  }

emptySymbolTable :: SymbolTable
emptySymbolTable  = MkSymbolTable
    { xtorNameMap = M.empty
    , typeNameMap =  M.empty
    , freeVarMap  = M.empty
    , tyOps       = []
    , imports     = []
    }

instance Show SymbolTable where
  show _ = "<SymbolTable>"

---------------------------------------------------------------------------------
-- Creating a SymbolTable
---------------------------------------------------------------------------------

-- | Creating a symbol table for a program.
-- Throws errors if multiple declarations declare the same name.
createSymbolTable :: MonadError Error m
                  => Program
                  -> m SymbolTable
createSymbolTable prog = createSymbolTableAcc prog emptySymbolTable
  where
    createSymbolTableAcc [] acc = pure acc
    createSymbolTableAcc (x:xs) acc = do
      acc' <- createSymbolTable' x acc
      createSymbolTableAcc xs acc'

createSymbolTable' :: MonadError Error m
                   => Declaration 
                   -> SymbolTable 
                   -> m SymbolTable
createSymbolTable' (XtorDecl _ _ dc xt args _) st = do
  let xtorResolve = XtorNameResult dc Structural (fst <$> args)
  pure $ st { xtorNameMap = M.insert xt xtorResolve (xtorNameMap st)}
createSymbolTable' (DataDecl _ _ NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors }) st = do
  -- Create the default polykind
  let polyKind = case data_kind of
                    Nothing -> MkPolyKind [] (case data_polarity of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
  let ns = case data_refined of
               Refined -> Refinement
               NotRefined -> Nominal
  let xtors = M.fromList [(sig_name xt, XtorNameResult data_polarity ns (linearContextToArity (sig_args xt)))| xt <- data_xtors]
  pure $ st { xtorNameMap = M.union xtors (xtorNameMap st)
            , typeNameMap = M.insert data_name (NominalResult data_polarity data_refined polyKind) (typeNameMap st)}
createSymbolTable' (TyOpDecl _ _ op prec assoc ty) st = do
    let tyOp = MkTyOp { symbol = CustomOp op
                      , prec = prec
                      , assoc = assoc
                      , desugar = NominalDesugaring ty
                      }
    pure $ st { tyOps = tyOp : (tyOps st) }
createSymbolTable' (ImportDecl loc _ mn) st =
  pure $ st { imports = (mn,loc):(imports st) }
createSymbolTable' (TySynDecl _ _ nm ty) st =
  pure $ st { typeNameMap = M.insert nm (SynonymResult ty) (typeNameMap st) }
createSymbolTable' _decl st = pure $ st