module Syntax.Common.TypesPol where

import Data.Set (Set)
import Data.Set qualified as S
import Data.Map (Map)
import Data.Map qualified as M
import Data.Kind ( Type )

import Syntax.Common
import Utils

------------------------------------------------------------------------------
-- CovContraList
------------------------------------------------------------------------------

data VariantType (pol :: Polarity) where
  CovariantType :: Typ pol -> VariantType pol
  ContravariantType :: Typ (FlipPol pol) -> VariantType pol

deriving instance Eq (VariantType pol)
deriving instance Ord (VariantType pol)
deriving instance Show (VariantType pol)

toVariance :: VariantType pol -> Variance
toVariance (CovariantType _) = Covariant
toVariance (ContravariantType _) = Contravariant

------------------------------------------------------------------------------
-- LinearContexts
------------------------------------------------------------------------------

data PrdCnsType (pol :: Polarity) where
  PrdCnsType :: PrdCnsRep pc -> Typ (PrdCnsFlip pc pol) -> PrdCnsType pol

instance Eq (PrdCnsType pol) where
  (PrdCnsType PrdRep ty1) == (PrdCnsType PrdRep ty2) = ty1 == ty2
  (PrdCnsType CnsRep ty1) == (PrdCnsType CnsRep ty2) = ty1 == ty2
  _ == _ = False

instance Ord (PrdCnsType pol) where
  (PrdCnsType PrdRep ty1) `compare` (PrdCnsType PrdRep ty2) = ty1 `compare` ty2
  (PrdCnsType CnsRep ty1) `compare` (PrdCnsType CnsRep ty2) = ty1 `compare` ty2
  (PrdCnsType PrdRep _)   `compare` (PrdCnsType CnsRep _)   = LT
  (PrdCnsType CnsRep _)   `compare` (PrdCnsType PrdRep _)   = GT

instance Show (PrdCnsType pol) where
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

deriving instance Eq (XtorSig pol)
deriving instance Ord (XtorSig pol)
deriving instance Show (XtorSig pol)

data Typ (pol :: Polarity) where
  TyVar :: Loc -> PolarityRep pol -> Maybe MonoKind -> TVar -> Typ pol
  -- | We have to duplicate TyStructData and TyStructCodata here due to restrictions of the deriving mechanism of Haskell.
  -- | Refinement types are represented by the presence of the TypeName parameter
  TyData   :: Loc -> PolarityRep pol -> Maybe RnTypeName -> [XtorSig pol]   -> Typ pol
  TyCodata :: Loc -> PolarityRep pol -> Maybe RnTypeName -> [XtorSig (FlipPol pol)] -> Typ pol
  -- | Nominal types with arguments to type parameters (contravariant, covariant)
  TyNominal :: Loc -> PolarityRep pol -> Maybe MonoKind -> RnTypeName -> [VariantType pol] -> Typ pol
  -- | Type synonym
  TySyn :: Loc -> PolarityRep pol -> RnTypeName -> Typ pol -> Typ pol
  -- | Lattice types
  TyBot :: Loc -> Maybe MonoKind -> Typ Pos
  TyTop :: Loc -> Maybe MonoKind -> Typ Neg
  TyUnion :: Loc -> Maybe MonoKind -> Typ Pos -> Typ Pos -> Typ Pos
  TyInter :: Loc -> Maybe MonoKind -> Typ Neg -> Typ Neg -> Typ Neg
  -- | Equirecursive Types
  TyRec :: Loc -> PolarityRep pol -> TVar -> Typ pol -> Typ pol
  -- | Builtin Types
  TyPrim :: Loc -> PolarityRep pol -> PrimitiveType -> Typ pol

flipTyp :: PolarityRep pol -> Typ pol -> Typ (FlipPol pol)
flipTyp pr (TyVar loc _ mk tv) = TyVar loc (flipPolarityRep pr) mk tv
flipTyp pr (TyData loc _ rn xtors) = TyData loc (flipPolarityRep pr) rn (flipXtorSig pr <$> xtors)
flipTyp pr (TyCodata loc _ rn xtors) = TyCodata loc (flipPolarityRep pr) rn (flipXtorSig (flipPolarityRep pr) <$> xtors)
flipTyp pr (TyNominal loc _ mk rn vts) = TyNominal loc (flipPolarityRep pr) mk rn (flipVariantType pr <$> vts)
flipTyp pr (TySyn loc _ rn ty) = TySyn loc (flipPolarityRep pr) rn (flipTyp pr ty)
flipTyp pr (TyRec loc _ tv ty) = TyRec loc (flipPolarityRep pr) tv (flipTyp pr ty)
flipTyp pr (TyPrim loc _ pt) = TyPrim loc (flipPolarityRep pr) pt
flipTyp _pr t = error $ "flipTyp: Cannot flip type " ++ show t

flipXtorSig :: PolarityRep pol -> XtorSig pol -> XtorSig (FlipPol pol)
flipXtorSig pr (MkXtorSig xt args) = MkXtorSig xt (f pr <$> args)
  where 
    f :: PolarityRep pol -> PrdCnsType pol -> PrdCnsType (FlipPol pol)
    f PosRep  (PrdCnsType PrdRep t) = PrdCnsType CnsRep t
    f NegRep  (PrdCnsType CnsRep t) = PrdCnsType PrdRep t
    f PosRep  (PrdCnsType CnsRep t) = PrdCnsType PrdRep t
    f NegRep  (PrdCnsType PrdRep t) = PrdCnsType CnsRep t

flipVariantType :: PolarityRep pol ->  VariantType pol -> VariantType (FlipPol pol)
flipVariantType pr (CovariantType x)= CovariantType (flipTyp pr x)
flipVariantType pr (ContravariantType x)= ContravariantType (flipTyp (flipPolarityRep pr) x)

deriving instance Eq (Typ pol)
deriving instance Ord (Typ pol)
deriving instance Show (Typ pol)

mkUnion :: Loc -> Maybe MonoKind -> [Typ Pos] -> Typ Pos
mkUnion loc knd []     = TyBot loc knd
mkUnion _   _   [t]    = t
mkUnion loc knd (t:ts) = TyUnion loc knd t (mkUnion loc knd ts)

mkInter :: Loc -> Maybe MonoKind -> [Typ Neg] -> Typ Neg
mkInter loc knd []     = TyTop loc knd
mkInter _   _   [t]    = t
mkInter loc knd (t:ts) = TyInter loc knd t (mkInter loc knd ts)

getPolarity :: Typ pol -> PolarityRep pol
getPolarity (TyVar _ rep _ _)         = rep
getPolarity (TyData _ rep _ _)        = rep
getPolarity (TyCodata _ rep _ _)      = rep
getPolarity (TyNominal _ rep _ _ _)   = rep
getPolarity (TySyn _ rep _ _)         = rep
getPolarity TyTop {}                  = NegRep
getPolarity TyBot {}                  = PosRep
getPolarity TyUnion {}                = PosRep
getPolarity TyInter {}                = NegRep
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
  freeTVars (TyVar _ _ _ tv)         = S.singleton tv
  freeTVars TyTop {}                 = S.empty
  freeTVars TyBot {}                 = S.empty
  freeTVars (TyUnion _ _ ty ty')     = S.union (freeTVars ty) (freeTVars ty')
  freeTVars (TyInter _ _ ty ty')     = S.union (freeTVars ty) (freeTVars ty')
  freeTVars (TyRec _ _ v t)          = S.delete v (freeTVars t)
  freeTVars (TyNominal _ _ _ _ args) = S.unions (freeTVars <$> args)
  freeTVars (TySyn _ _ _ ty)         = freeTVars ty
  freeTVars (TyData _ _ _ xtors)     = S.unions (freeTVars <$> xtors)
  freeTVars (TyCodata _ _ _ xtors)   = S.unions (freeTVars <$> xtors)
  freeTVars (TyPrim _ _ _)           = S.empty

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
  zonk _ (TyTop loc knd) =
    TyTop loc knd
  zonk _ (TyBot loc knd) =
    TyBot loc knd
  zonk bisubst (TyUnion loc knd ty ty') =
    TyUnion loc knd (zonk bisubst ty) (zonk bisubst ty')
  zonk bisubst (TyInter loc knd ty ty') =
    TyInter loc knd (zonk bisubst ty) (zonk bisubst ty')
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
