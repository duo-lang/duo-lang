module Syntax.CST.Types where

import qualified Syntax.AST.Types as AST
import Syntax.CommonTerm
import Syntax.Kinds
import Data.List.NonEmpty (NonEmpty)

---------------------------------------------------------------------------------
-- Parse Types
---------------------------------------------------------------------------------
data BinOp where
  FunOp    :: BinOp
  ParOp    :: BinOp
  UnionOp  :: BinOp
  InterOp  :: BinOp
  deriving (Show, Eq)


data Typ where
  TyVar :: AST.TVar -> Typ
  TyXData :: AST.DataCodata -> Maybe AST.TypeName -> [XtorSig] -> Typ
  TyNominal :: AST.TypeName -> [Typ] -> Typ
  TyRec :: AST.TVar -> Typ -> Typ
  TyTop :: Typ
  TyBot :: Typ
  -- | A chain of binary type operators generated by the parser
  -- Lowering will replace "TyBinOpChain" nodes with "TyBinOp" nodes.
  TyBinOpChain :: Typ -> NonEmpty (BinOp, Typ) -> Typ
  -- | A binary type operator waiting to be desugared
  -- This is used as an intermediate representation by lowering and
  -- should never be directly constructed elsewhere.
  TyBinOp :: Typ -> BinOp -> Typ -> Typ
  TyParens :: Typ -> Typ
  deriving Show

data XtorSig = MkXtorSig
  { sig_name :: XtorName
  , sig_args :: LinearContext
  }
  deriving Show

type LinearContext = [PrdCnsTyp]

data PrdCnsTyp where
  PrdType :: Typ -> PrdCnsTyp
  CnsType :: Typ -> PrdCnsTyp
  deriving Show

data TypeScheme = TypeScheme
  { ts_vars :: [AST.TVar]
  , ts_monotype :: Typ
  }
  deriving Show

------------------------------------------------------------------------------
-- Data Type declarations
------------------------------------------------------------------------------

data DataDecl = NominalDecl
  { data_refined :: AST.IsRefined
  , data_name :: AST.TypeName
  , data_polarity :: AST.DataCodata
  , data_kind :: Kind
  , data_xtors :: [XtorSig]
  , data_params :: AST.TParams
  }
