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
  , defs :: Map FreeVarName ()
  , imports :: [(ModuleName, Loc)]
  }

emptySymbolTable :: SymbolTable
emptySymbolTable = MkSymbolTable
    { xtorMap = M.empty
    , tyConMap =  M.empty
    , tyOps = [unionTyOp, interTyOp]
    , defs = M.empty
    , imports = []
    }

instance Show SymbolTable where
  show _ = "<SymbolTable>"

---------------------------------------------------------------------------------
-- Creating a SymbolTable
---------------------------------------------------------------------------------

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
createSymbolTable' (XtorDecl _ _ dc xt args _) st =
  pure $ st { xtorMap = M.insert (xt,dc) (Structural, fst <$> args) (xtorMap st)}
createSymbolTable' (DataDecl _ _ NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors }) st = do
  -- Create the default polykind
  let polyKind = case data_kind of
                    Nothing -> MkPolyKind [] (case data_polarity of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
  let ns = case data_refined of
               Refined -> Refinement
               NotRefined -> Nominal
  let xtors = M.fromList [((sig_name xt, data_polarity), (ns, linearContextToArity (sig_args xt)))| xt <- data_xtors]
  pure $ st { xtorMap  = M.union xtors (xtorMap st)
            , tyConMap = M.insert data_name (NominalResult data_refined polyKind) (tyConMap st)}
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
  pure $ st { tyConMap = M.insert nm (SynonymResult ty) (tyConMap st) }
createSymbolTable' _decl st = pure $ st