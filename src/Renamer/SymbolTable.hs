module Renamer.SymbolTable where

import Data.Map (Map)
import Data.Map qualified as M

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

-- | Type operator for the union type
unionTyOp :: TyOp
unionTyOp = MkTyOp
  { symbol = UnionOp
  , prec = MkPrecedence 1
  , assoc = LeftAssoc
  , desugar = UnionDesugaring
  }

-- | Type operator for the intersection type
interTyOp :: TyOp
interTyOp = MkTyOp
  { symbol = InterOp
  , prec = MkPrecedence 2
  , assoc = LeftAssoc
  , desugar = InterDesugaring
  }

---------------------------------------------------------------------------------
-- Symbol Table
---------------------------------------------------------------------------------

data TyConResult =
    NominalResult IsRefined PolyKind
  | SynonymResult Typ

data SymbolTable = MkSymbolTable
  { xtorMap :: Map (XtorName,DataCodata) (NominalStructural, Arity)
  , tyConMap :: Map TypeName TyConResult
  , tyOps :: [TyOp]
  , imports :: [(ModuleName, Loc)]
  }

instance Show SymbolTable where
  show _ = "<SymbolTable>"

instance Semigroup SymbolTable where
  (MkSymbolTable xtormap1 tyConMap1 tyOps1 imports1) <> (MkSymbolTable xtormap2 tyConMap2 tyOps2 imports2) =
    MkSymbolTable (M.union xtormap1 xtormap2) (M.union tyConMap1 tyConMap2) (tyOps1 ++ tyOps2) (imports1 ++ imports2)

instance Monoid SymbolTable where
  mempty = MkSymbolTable
    { xtorMap = M.empty
    , tyConMap =  M.empty
    , tyOps = [unionTyOp, interTyOp]
    , imports = []
    }

---------------------------------------------------------------------------------
-- Creating a SymbolTable
---------------------------------------------------------------------------------

createSymbolTable :: Program -> SymbolTable
createSymbolTable = foldr createSymbolTable' mempty

createSymbolTable' :: Declaration -> SymbolTable -> SymbolTable
createSymbolTable' (XtorDecl _ _ dc xt args _) st =
  st { xtorMap = M.insert (xt,dc) (Structural, fst <$> args) (xtorMap st)}
createSymbolTable' (DataDecl _ _ NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors }) st =
  -- Create the default polykind
  let polyKind = case data_kind of
                    Nothing -> MkPolyKind [] (case data_polarity of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
      ns = case data_refined of
               Refined -> Refinement
               NotRefined -> Nominal
      xtors = M.fromList [((sig_name xt, data_polarity), (ns, linearContextToArity (sig_args xt)))| xt <- data_xtors]
  in st { xtorMap  = M.union xtors (xtorMap st)
        , tyConMap = M.insert data_name (NominalResult data_refined polyKind) (tyConMap st)}
createSymbolTable' (TyOpDecl _ _ op prec assoc ty) st =
    let tyOp = MkTyOp { symbol = CustomOp op
                      , prec = prec
                      , assoc = assoc
                      , desugar = NominalDesugaring ty
                      }
    in st { tyOps = tyOp : (tyOps st) }
createSymbolTable' (ImportDecl loc _ mn) st =
  st { imports = (mn,loc):(imports st) }
createSymbolTable' (TySynDecl _ _ nm ty) st =
  st { tyConMap = M.insert nm (SynonymResult ty) (tyConMap st) }
createSymbolTable' _decl st = st