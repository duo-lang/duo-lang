module Syntax.CST.Types where

import Syntax.CST.Names
    ( BinOp, SkolemTVar, TypeName, XtorName )
import Syntax.CST.Kinds
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

type Arity = [PrdCns]

---------------------------------------------------------------------------------
-- Parse Types
---------------------------------------------------------------------------------

data DataCodata = Data | Codata deriving (Eq, Ord, Show)

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


data TypeScheme = TypeScheme
  { loc :: Loc
  , vars :: [MaybeKindedSkolem]
  , monotype :: Typ
  }
  deriving Show

instance HasLoc TypeScheme where
  getLoc ts = ts.loc
