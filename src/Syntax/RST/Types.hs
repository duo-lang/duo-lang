module Syntax.RST.Types where

import Data.Set (Set)
import Data.Set qualified as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.Kind ( Type )

import Syntax.Common
import Utils

------------------------------------------------------------------------------
-- CovContraList
------------------------------------------------------------------------------

data VariantType (pol :: Polarity) where
  CovariantType :: Typ pol -> VariantType pol
  ContravariantType :: Typ (FlipPol pol) -> VariantType pol

deriving instance Eq (VariantType Pos)
deriving instance Eq (VariantType Neg)
deriving instance Ord (VariantType Pos)
deriving instance Ord (VariantType Neg)
deriving instance Show (VariantType Pos)
deriving instance Show (VariantType Neg)

toVariance :: VariantType pol -> Variance
toVariance (CovariantType _) = Covariant
toVariance (ContravariantType _) = Contravariant

------------------------------------------------------------------------------
-- LinearContexts
------------------------------------------------------------------------------

data PrdCnsType (pol :: Polarity) where
  PrdCnsType :: PrdCnsRep pc -> Typ (PrdCnsFlip pc pol) -> PrdCnsType pol

instance Eq (PrdCnsType Pos) where
  (PrdCnsType PrdRep ty1) == (PrdCnsType PrdRep ty2) = ty1 == ty2
  (PrdCnsType CnsRep ty1) == (PrdCnsType CnsRep ty2) = ty1 == ty2
  _ == _ = False
instance Eq (PrdCnsType Neg) where
  (PrdCnsType PrdRep ty1) == (PrdCnsType PrdRep ty2) = ty1 == ty2
  (PrdCnsType CnsRep ty1) == (PrdCnsType CnsRep ty2) = ty1 == ty2
  _ == _ = False
-- For Ord: PrdType < CnsType
instance Ord (PrdCnsType Pos) where
  (PrdCnsType PrdRep ty1) `compare` (PrdCnsType PrdRep ty2) = ty1 `compare` ty2
  (PrdCnsType CnsRep ty1) `compare` (PrdCnsType CnsRep ty2) = ty1 `compare` ty2
  (PrdCnsType PrdRep _)   `compare` (PrdCnsType CnsRep _)   = LT
  (PrdCnsType CnsRep _)   `compare` (PrdCnsType PrdRep _)   = GT
instance Ord (PrdCnsType Neg) where
  (PrdCnsType PrdRep ty1) `compare` (PrdCnsType PrdRep ty2) = ty1 `compare` ty2
  (PrdCnsType CnsRep ty1) `compare` (PrdCnsType CnsRep ty2) = ty1 `compare` ty2
  (PrdCnsType PrdRep _)   `compare` (PrdCnsType CnsRep _)   = LT
  (PrdCnsType CnsRep _)   `compare` (PrdCnsType PrdRep _)   = GT
instance Show (PrdCnsType Pos) where
  show (PrdCnsType PrdRep ty) = "PrdType " <> show ty
  show (PrdCnsType CnsRep ty) = "CnsType " <> show ty
instance Show (PrdCnsType Neg) where
  show (PrdCnsType PrdRep ty) = "PrdType " <> show ty
  show (PrdCnsType CnsRep ty) = "CnsType " <> show ty

type LinearContext pol = [PrdCnsType pol]

linearContextToArity :: LinearContext pol -> Arity
linearContextToArity = map f
  where
    f :: PrdCnsType pol -> PrdCns
    f (PrdCnsType PrdRep _) = Prd
    f (PrdCnsType CnsRep _) = Cns

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

data XtorSig (pol :: Polarity) = MkXtorSig
  { sig_name :: XtorName
  , sig_args :: LinearContext pol
  }

deriving instance Eq (XtorSig Pos)
deriving instance Eq (XtorSig Neg)
deriving instance Ord (XtorSig Pos)
deriving instance Ord (XtorSig Neg)
deriving instance Show (XtorSig Pos)
deriving instance Show (XtorSig Neg)

data Typ (pol :: Polarity) where
  TyVar :: Loc -> PolarityRep pol -> Maybe MonoKind -> TVar -> Typ pol
  -- | We have to duplicate TyStructData and TyStructCodata here due to restrictions of the deriving mechanism of Haskell.
  -- | Refinement types are represented by the presence of the TypeName parameter
  TyData :: Loc -> PolarityRep pol -> Maybe RnTypeName -> [XtorSig pol]   -> Typ pol
  TyCodata :: Loc -> PolarityRep pol -> Maybe RnTypeName -> [XtorSig (FlipPol pol)] -> Typ pol
  -- | Nominal types with arguments to type parameters (contravariant, covariant)
  TyNominal :: Loc -> PolarityRep pol -> Maybe MonoKind -> RnTypeName -> [VariantType pol] -> Typ pol
  -- | Type synonym
  TySyn :: Loc -> PolarityRep pol -> RnTypeName -> Typ pol -> Typ pol
  -- | PosRep = Union, NegRep = Intersection
  TySet :: Loc -> PolarityRep pol -> Maybe MonoKind -> [Typ pol] -> Typ pol
  TyRec :: Loc -> PolarityRep pol -> TVar -> Typ pol -> Typ pol
  TyPrim :: Loc -> PolarityRep pol -> PrimitiveType -> Typ pol

deriving instance Eq (Typ Pos)
deriving instance Eq (Typ Neg)
deriving instance Ord (Typ Pos)
deriving instance Ord (Typ Neg)
deriving instance Show (Typ Pos)
deriving instance Show (Typ Neg)

getPolarity :: Typ pol -> PolarityRep pol
getPolarity (TyVar _ rep _ _)         = rep
getPolarity (TyData _ rep _ _)        = rep
getPolarity (TyCodata _ rep _ _)      = rep
getPolarity (TyNominal _ rep _ _ _)   = rep
getPolarity (TySyn _ rep _ _)         = rep
getPolarity (TySet _ rep _ _)         = rep
getPolarity (TyRec _ rep _ _)         = rep
getPolarity (TyPrim _ rep _)          = rep

------------------------------------------------------------------------------
-- Type Schemes
------------------------------------------------------------------------------

data TypeScheme (pol :: Polarity) = TypeScheme
  { ts_loc :: Loc
  , ts_vars :: [TVar]
  , ts_monotype :: Typ pol
  }

deriving instance Eq (TypeScheme Pos)
deriving instance Eq (TypeScheme Neg)
deriving instance Ord (TypeScheme Pos)
deriving instance Ord (TypeScheme Neg)
deriving instance Show (TypeScheme Pos)
deriving instance Show (TypeScheme Neg)

data TopAnnot (pol :: Polarity) where
  Annotated :: TypeScheme pol -> TopAnnot pol
  Inferred  :: TypeScheme pol -> TopAnnot pol

deriving instance Show (TopAnnot Pos)
deriving instance Show (TopAnnot Neg)


-- | Typeclass for computing free type variables
class FreeTVars (a :: Type) where
  freeTVars :: a -> Set TVar

instance FreeTVars (Typ pol) where
  freeTVars (TyVar _ _ _ tv) = S.singleton tv
  freeTVars (TySet _ _ _ ts) = S.unions (freeTVars <$> ts)
  freeTVars (TyRec _ _ v t)  = S.delete v (freeTVars t)
  freeTVars (TyNominal _ _ _ _ args) = S.unions (freeTVars <$> args)
  freeTVars (TySyn _ _ _ ty) = freeTVars ty
  freeTVars (TyData _ _ _ xtors) = S.unions (freeTVars <$> xtors)
  freeTVars (TyCodata _ _ _ xtors) = S.unions (freeTVars <$> xtors)
  freeTVars (TyPrim _ _ _) = S.empty

instance FreeTVars (PrdCnsType pol) where
  freeTVars (PrdCnsType _ ty) = freeTVars ty
    
instance FreeTVars (VariantType pol) where
  freeTVars (CovariantType ty)     = freeTVars ty
  freeTVars (ContravariantType ty) = freeTVars ty

instance FreeTVars (LinearContext pol) where
  freeTVars ctxt = S.unions (freeTVars <$> ctxt)

instance FreeTVars (XtorSig pol) where
  freeTVars (MkXtorSig { sig_args }) = freeTVars sig_args

-- | Generalize over all free type variables of a type.
generalize :: Typ pol -> TypeScheme pol
generalize ty = TypeScheme defaultLoc (S.toList (freeTVars ty)) ty

------------------------------------------------------------------------------
-- Bisubstitution and Zonking
------------------------------------------------------------------------------

data Bisubstitution = MkBisubstitution { uvarSubst :: Map TVar (Typ Pos, Typ Neg) }

-- | Class of types for which a Bisubstitution can be applied.
class Zonk (a :: Type) where
  zonk :: Bisubstitution -> a -> a

instance Zonk (Typ pol) where
  zonk bisubst ty@(TyVar _ PosRep _ tv) = case M.lookup tv (uvarSubst bisubst) of
     Nothing -> ty -- Recursive variable!
     Just (tyPos,_) -> tyPos
  zonk bisubst ty@(TyVar _ NegRep _ tv) = case M.lookup tv (uvarSubst bisubst) of
     Nothing -> ty -- Recursive variable!
     Just (_,tyNeg) -> tyNeg
  zonk bisubst (TyData loc rep tn xtors) =
     TyData loc rep tn (zonk bisubst <$> xtors)
  zonk bisubst (TyCodata loc rep tn xtors) =
     TyCodata loc rep tn (zonk bisubst <$> xtors)
  zonk bisubst (TyNominal loc rep kind tn args) =
     TyNominal loc rep kind tn (zonk bisubst <$> args)
  zonk bisubst (TySyn loc rep nm ty) =
     TySyn loc rep nm (zonk bisubst ty)
  zonk bisubst (TySet loc rep kind tys) =
     TySet loc rep kind (zonk bisubst <$> tys)
  zonk bisubst (TyRec loc rep tv ty) =
     TyRec loc rep tv (zonk bisubst ty)
  zonk _ t@TyPrim {} = t

instance Zonk (VariantType pol) where
  zonk bisubst (CovariantType ty) = CovariantType (zonk bisubst ty)
  zonk bisubst (ContravariantType ty) = ContravariantType (zonk bisubst ty)

instance Zonk (XtorSig pol) where
  zonk bisubst (MkXtorSig name ctxt) =
    MkXtorSig name (zonk bisubst ctxt)

instance Zonk (LinearContext pol) where
  zonk bisubst = fmap (zonk bisubst)

instance Zonk (PrdCnsType pol) where
  zonk bisubst (PrdCnsType rep ty) = PrdCnsType rep (zonk bisubst ty)


-- This is probably not 100% correct w.r.t alpha-renaming. Postponed until we have a better repr. of types.
unfoldRecType :: Typ pol -> Typ pol
unfoldRecType recty@(TyRec _ PosRep var ty) = zonk (MkBisubstitution (M.fromList [(var,(recty, error "unfoldRecType"))])) ty
unfoldRecType recty@(TyRec _ NegRep var ty) = zonk (MkBisubstitution (M.fromList [(var,(error "unfoldRecType", recty))])) ty
unfoldRecType ty = ty

------------------------------------------------------------------------------
-- Data Type declarations
------------------------------------------------------------------------------

data DataDecl = NominalDecl
  { data_refined :: IsRefined
  , data_name :: RnTypeName
  , data_polarity :: DataCodata
  , data_kind :: PolyKind
  , data_xtors :: ([XtorSig Pos], [XtorSig Neg])
  } deriving (Show)
