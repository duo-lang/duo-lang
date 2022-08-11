module Syntax.CST.Types where

import Syntax.CST.Names
    ( BinOp, ClassName, SkolemTVar, TypeName, UniTVar, XtorName )
import Syntax.Common.PrdCns ( Arity, PrdCns(Cns, Prd) )

import Data.List.NonEmpty (NonEmpty)
import Utils ( Loc, HasLoc(..))

---------------------------------------------------------------------------------
-- Parse Types
---------------------------------------------------------------------------------

data DataCodata = Data | Codata deriving (Eq, Ord, Show)

data Typ where
  TyUniVar :: Loc -> UniTVar -> Typ
  TySkolemVar :: Loc -> SkolemTVar -> Typ
  TyXData    :: Loc -> DataCodata             -> [XtorSig] -> Typ
  TyXRefined :: Loc -> DataCodata -> TypeName -> [XtorSig] -> Typ
  TyNominal :: Loc -> TypeName -> [Typ] -> Typ
  TyRec :: Loc -> SkolemTVar -> Typ -> Typ
  TyTop :: Loc -> Typ
  TyBot :: Loc -> Typ
  TyI64 :: Loc -> Typ
  TyF64 :: Loc -> Typ
  TyChar :: Loc -> Typ
  TyString :: Loc -> Typ
  -- | A chain of binary type operators generated by the parser
  -- Lowering will replace "TyBinOpChain" nodes with "TyBinOp" nodes.
  TyBinOpChain :: Typ -> NonEmpty (Loc, BinOp,  Typ) -> Typ
  -- | A binary type operator waiting to be desugared
  -- This is used as an intermediate representation by lowering and
  -- should never be directly constructed elsewhere.
  TyBinOp :: Loc -> Typ -> BinOp -> Typ -> Typ
  TyParens :: Loc -> Typ -> Typ
  deriving Show

instance HasLoc Typ where
  getLoc (TyUniVar loc _) = loc
  getLoc (TySkolemVar loc _) = loc
  getLoc (TyXData loc _ _) = loc
  getLoc (TyXRefined loc _ _ _) = loc
  getLoc (TyNominal loc _ _) = loc
  getLoc (TyRec loc _ _) = loc
  getLoc (TyTop loc) = loc
  getLoc (TyBot loc) = loc
  getLoc (TyI64 loc) = loc
  getLoc (TyF64 loc) = loc
  getLoc (TyChar loc) = loc
  getLoc (TyString loc) = loc
  -- Implementation of getLoc for TyBinOpChain a bit hacky!
  getLoc (TyBinOpChain ty _) = getLoc ty
  getLoc (TyBinOp loc _ _ _) = loc
  getLoc (TyParens loc _) = loc

data XtorSig = MkXtorSig
  { sig_name :: XtorName
  , sig_args :: LinearContext
  }
  deriving Show

data PrdCnsTyp where
  PrdType :: Typ -> PrdCnsTyp
  CnsType :: Typ -> PrdCnsTyp
  deriving Show

type LinearContext = [PrdCnsTyp]

linearContextToArity :: LinearContext -> Arity
linearContextToArity = map f
  where
    f (PrdType _) = Prd
    f (CnsType _) = Cns

data TypeScheme = TypeScheme
  { ts_loc :: Loc
  , ts_vars :: [SkolemTVar]
  , ts_constraints :: [Constraint]
  , ts_monotype :: Typ
  }
  deriving Show

instance HasLoc TypeScheme where
  getLoc ts = ts_loc ts

---------------------------------------------------------------------------------
-- Constraints
---------------------------------------------------------------------------------

data Constraint
  = SubType Typ Typ
  | TypeClass ClassName SkolemTVar
 deriving Show

