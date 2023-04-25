module Syntax.CST.Types where

import Syntax.CST.Names
    ( BinOp, SkolemTVar, TypeName, XtorName, KVar )
import Data.List.NonEmpty (NonEmpty)
import Loc ( Loc, HasLoc(..))

---------------------------------------------------------------------------------
-- Producer / Consumer
---------------------------------------------------------------------------------

data PrdCns
  = Prd
  | Cns
  deriving (Eq, Show, Ord)

-- | Singleton Type for PrdCns
data PrdCnsRep pc where
  PrdRep :: PrdCnsRep Prd
  CnsRep :: PrdCnsRep Cns
deriving instance Show (PrdCnsRep pc)
deriving instance Eq (PrdCnsRep pc)

---------------------------------------------------------------------------------
-- Variance
---------------------------------------------------------------------------------

data Variance = Covariant | Contravariant
  deriving (Eq, Show, Ord)

instance Semigroup Variance where
  Covariant <> v         = v
  v         <> Covariant = v
  _         <> _         = Covariant

---------------------------------------------------------------------------------
-- Evaluation Order
---------------------------------------------------------------------------------

-- | An evaluation order is either call-by-value or call-by-name.
data EvaluationOrder = CBV | CBN
  deriving (Show, Eq, Ord)

---------------------------------------------------------------------------------
-- Arity
---------------------------------------------------------------------------------

type Arity = [PrdCns]

---------------------------------------------------------------------------------
-- DataCodata
---------------------------------------------------------------------------------

data DataCodata = Data | Codata deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------
-- Parse Types
---------------------------------------------------------------------------------

data Typ where
  TySkolemVar :: Loc -> SkolemTVar -> Typ
  TyXData    :: Loc -> DataCodata             -> [XtorSig] -> Typ
  TyXRefined :: Loc -> DataCodata -> TypeName -> [XtorSig] -> Typ
  TyNominal :: Loc -> TypeName -> Typ
  TyApp :: Loc -> Typ -> Maybe TypeName -> NonEmpty Typ -> Typ
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
  TyKindAnnot :: MonoKind -> Typ -> Typ
  deriving (Show, Eq)

getTypeName :: Typ -> Maybe TypeName
getTypeName (TyXRefined _ _ tyn _) = Just tyn
getTypeName (TyNominal _ tyn) = Just tyn
getTypeName (TyRec _ _ ty) = getTypeName ty
getTypeName (TyParens _ ty) = getTypeName ty 
getTypeName (TyKindAnnot _ ty) = getTypeName ty 
getTypeName _ = Nothing 

instance HasLoc Typ where
  getLoc (TySkolemVar loc _) = loc
  getLoc (TyXData loc _ _) = loc
  getLoc (TyXRefined loc _ _ _) = loc
  getLoc (TyNominal loc _ ) = loc
  getLoc (TyApp loc _  _ _) = loc
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
  getLoc (TyKindAnnot _ ty) = getLoc ty


data XtorSig = MkXtorSig
  { name :: XtorName
  , args :: LinearContext
  }
  deriving (Show, Eq)

data PrdCnsTyp where
  PrdType :: Typ -> PrdCnsTyp
  CnsType :: Typ -> PrdCnsTyp
  deriving (Show, Eq)

type LinearContext = [PrdCnsTyp]

linearContextToArity :: LinearContext -> Arity
linearContextToArity = map f
  where
    f (PrdType _) = Prd
    f (CnsType _) = Cns


---------------------------------------------------------------------------------
-- MonoKind
---------------------------------------------------------------------------------

-- | A MonoKind is a kind which classifies inhabitated types.
data MonoKind where
  CBox :: EvaluationOrder -> MonoKind
  -- ^ Boxed CBV/CBN
  I64Rep :: MonoKind
  F64Rep :: MonoKind
  CharRep :: MonoKind
  StringRep :: MonoKind

deriving instance Show MonoKind
deriving instance Eq MonoKind
deriving instance Ord MonoKind

------------------------------------------------------------------------------
-- PolyKinds and TypeSchemes
------------------------------------------------------------------------------

data PolyKind =
  MkPolyKind { kindArgs :: [(Variance, SkolemTVar, MonoKind)]
             , returnKind :: EvaluationOrder
             }
  | KindVar KVar 

deriving instance Show PolyKind
deriving instance Ord PolyKind
instance Eq PolyKind where 
  KindVar kv1 == KindVar kv2 = kv1 == kv2
  MkPolyKind args1 eo1 == MkPolyKind args2 eo2 = 
    let getVariances = Prelude.map (\(x,_,_) -> x)
        getMks = Prelude.map (\(_,_,z) -> z)
    in 
    eo1 == eo2 && getVariances args1 == getVariances args2 && getMks args1 == getMks args2
  _ == _ = False 

data TypeScheme = TypeScheme
  { loc :: Loc
  , vars :: [(SkolemTVar, Maybe PolyKind)]
  , monotype :: Typ
  }
  deriving Show

instance HasLoc TypeScheme where
  getLoc ts = ts.loc