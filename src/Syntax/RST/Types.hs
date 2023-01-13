module Syntax.RST.Types where 

import Data.Set (Set)
import Data.Set qualified as S
import Data.Kind ( Type )
import Data.List.NonEmpty (NonEmpty)

import Syntax.CST.Kinds ( Variance(..),MaybeKindedSkolem, MonoKind(..), PolyKind(..))
import Syntax.CST.Types ( PrdCnsRep(..), PrdCns(..), Arity)
import Syntax.CST.Names
    ( MethodName, RecTVar, RnTypeName, SkolemTVar, UniTVar, XtorName )
import Loc ( Loc, defaultLoc, HasLoc(..) )

------------------------------------------------------------------------------
-- Polarity
------------------------------------------------------------------------------

data Polarity = Pos | Neg deriving (Eq, Ord, Show)

data PolarityRep pol where
  PosRep :: PolarityRep Pos
  NegRep :: PolarityRep Neg

deriving instance Show (PolarityRep pol)
deriving instance Eq (PolarityRep pol)
deriving instance Ord (PolarityRep pol)

flipPol :: Polarity -> Polarity
flipPol Pos = Neg
flipPol Neg = Pos

type family FlipPol (pol :: Polarity) :: Polarity where
  FlipPol Pos = Neg
  FlipPol Neg = Pos

flipPolarityRep :: forall pol. PolarityRep pol -> PolarityRep (FlipPol pol)
flipPolarityRep PosRep = NegRep
flipPolarityRep NegRep = PosRep

polarityRepToPol :: PolarityRep pol -> Polarity
polarityRepToPol PosRep = Pos
polarityRepToPol NegRep = Neg

type family PrdCnsFlip (pc :: PrdCns) (pol :: Polarity) :: Polarity where
  PrdCnsFlip Prd pol = pol
  PrdCnsFlip Cns pol = FlipPol pol

type family FlipPrdCns (pc :: PrdCns) :: PrdCns where
  FlipPrdCns Prd = Cns
  FlipPrdCns Cns = Prd

flipPrdCns :: PrdCnsRep pc -> PrdCnsRep (FlipPrdCns pc)
flipPrdCns PrdRep = CnsRep
flipPrdCns CnsRep = PrdRep

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

data MethodSig (pol :: Polarity) = MkMethodSig
  { msig_name :: MethodName
  , msig_args :: [PrdCnsType pol]
  }

deriving instance Eq (MethodSig pol)
deriving instance Ord (MethodSig pol)
deriving instance Show (MethodSig pol)


data Typ (pol     :: Polarity) where
  TySkolemVar     :: Loc -> PolarityRep pol -> SkolemTVar -> Typ pol
  TyUniVar        :: Loc -> PolarityRep pol -> UniTVar -> Typ pol
  TyRecVar        :: Loc -> PolarityRep pol -> RecTVar -> Typ pol
  -- | We have to duplicate TyStructData and TyStructCodata here due to restrictions of the deriving mechanism of Haskell.
  -- | Refinement types are represented by the presence of the TypeName parameter
  TyData          :: Loc -> PolarityRep pol               -> [XtorSig pol]           -> Typ pol
  TyCodata        :: Loc -> PolarityRep pol               -> [XtorSig (FlipPol pol)] -> Typ pol
  TyDataRefined   :: Loc -> PolarityRep pol -> PolyKind -> RnTypeName -> [XtorSig pol]           -> Typ pol
  TyCodataRefined :: Loc -> PolarityRep pol -> PolyKind -> RnTypeName -> [XtorSig (FlipPol pol)] -> Typ pol
  -- | Nominal types with arguments to type parameters (contravariant, covariant)
  TyNominal       :: Loc -> PolarityRep pol -> PolyKind -> RnTypeName  -> Typ pol
  TyApp           :: Loc -> PolarityRep pol -> Typ pol -> NonEmpty (VariantType pol) -> Typ pol
  -- | Type synonym
  TySyn           :: Loc -> PolarityRep pol -> RnTypeName -> Typ pol -> Typ pol
  -- | Lattice types
  TyBot           :: Loc -> Typ Pos
  TyTop           :: Loc -> Typ Neg
  TyUnion         :: Loc -> Typ Pos -> Typ Pos -> Typ Pos
  TyInter         :: Loc -> Typ Neg -> Typ Neg -> Typ Neg
  -- | Equirecursive Types
  TyRec           :: Loc -> PolarityRep pol -> RecTVar -> Typ pol -> Typ pol
  -- | Builtin Types
  TyI64           :: Loc -> PolarityRep pol -> Typ pol
  TyF64           :: Loc -> PolarityRep pol -> Typ pol
  TyChar          :: Loc -> PolarityRep pol -> Typ pol
  TyString        :: Loc -> PolarityRep pol -> Typ pol
  -- | TyFlipPol is only generated during focusing, and cannot be parsed!
  TyFlipPol       :: PolarityRep pol -> Typ (FlipPol pol) -> Typ pol
  -- | Kind Annotated Type
  TyKindAnnot     :: MonoKind -> Typ pol -> Typ pol

deriving instance Eq (Typ pol)
deriving instance Ord (Typ pol)
deriving instance Show (Typ pol)

instance HasLoc (Typ pol) where 
  getLoc :: Typ pol -> Loc
  getLoc (TySkolemVar loc _ _)         = loc
  getLoc (TyUniVar loc _ _)            = loc
  getLoc (TyRecVar loc _ _)            = loc
  getLoc (TyData loc _ _)              = loc
  getLoc (TyCodata loc _ _)            = loc
  getLoc (TyDataRefined loc _ _ _ _)   = loc
  getLoc (TyCodataRefined loc _ _ _ _) = loc
  getLoc (TyNominal loc _ _ _)         = loc
  getLoc (TyApp loc _ _ _)             = loc
  getLoc (TySyn loc _ _ _)             = loc
  getLoc (TyBot loc)                   = loc
  getLoc (TyTop loc)                   = loc
  getLoc (TyUnion loc _ _ )            = loc 
  getLoc (TyInter loc _ _ )            = loc
  getLoc (TyRec loc _ _ _)             = loc
  getLoc (TyI64 loc _)                 = loc
  getLoc (TyF64 loc _)                 = loc
  getLoc (TyChar loc _)                = loc
  getLoc (TyString loc _)              = loc
  getLoc (TyFlipPol _ ty)              = getLoc ty
  getLoc (TyKindAnnot _ ty)            = getLoc ty

mkUnion :: Loc -> [Typ Pos] -> Typ Pos
mkUnion loc []     = TyBot loc 
mkUnion _   [t]    = t
mkUnion loc (t:ts) = TyUnion loc t (mkUnion loc ts)

mkInter :: Loc ->[Typ Neg] -> Typ Neg
mkInter loc []     = TyTop loc
mkInter _   [t]    = t
mkInter loc (t:ts) = TyInter loc t (mkInter loc ts)

getPolarity :: Typ pol -> PolarityRep pol
getPolarity (TySkolemVar _ rep  _)        = rep
getPolarity (TyUniVar _ rep  _)           = rep
getPolarity (TyRecVar _ rep  _)           = rep
getPolarity (TyData _ rep _)              = rep
getPolarity (TyCodata _ rep _)            = rep
getPolarity (TyDataRefined _ rep _ _ _)   = rep
getPolarity (TyCodataRefined _ rep _ _ _) = rep
getPolarity (TyNominal _ rep  _ _)        = rep
getPolarity (TyApp _ rep _ _)             = rep
getPolarity (TySyn _ rep _ _)             = rep
getPolarity TyTop {}                      = NegRep
getPolarity TyBot {}                      = PosRep
getPolarity TyUnion {}                    = PosRep
getPolarity TyInter {}                    = NegRep
getPolarity (TyRec _ rep _ _)             = rep
getPolarity (TyI64 _ rep)                 = rep
getPolarity (TyF64 _ rep)                 = rep
getPolarity (TyChar _ rep)                = rep
getPolarity (TyString _ rep)              = rep
getPolarity (TyFlipPol rep _)             = rep
getPolarity (TyKindAnnot _ ty)            = getPolarity ty


------------------------------------------------------------------------------
-- Replace a nominal type by a given type
--
-- These functions are used in the computation of refinement types:
-- We have to replace the user-written nominal type `Nat` by the refinement
-- type `rec alpha. < Nat | Z, S(alpha) >`, for example.
-- Similarly, we have to replace the constructor `S(Nat)` by the constructor
-- `S(rec alpha. < Nat | Z, S(alpha) >)` when we look up constructor signatures.
------------------------------------------------------------------------------

class ReplaceNominal a where
  replaceNominal :: Typ Pos -> Typ Neg -> RnTypeName -> a -> a

instance ReplaceNominal (Typ pol) where
  replaceNominal :: forall pol. Typ Pos -> Typ Neg -> RnTypeName -> Typ pol -> Typ pol
  replaceNominal _ _ _ ty@TySkolemVar{}                  = ty
  replaceNominal _ _ _ ty@TyUniVar{}                     = ty
  replaceNominal _ _ _ ty@TyRecVar{}                     = ty
  replaceNominal p n t (TyData loc rep args)             = TyData loc rep (replaceNominal p n t <$> args)
  replaceNominal p n t (TyCodata loc rep args)           = TyCodata loc rep (replaceNominal p n t <$> args)
  replaceNominal p n t (TyDataRefined loc rep pknd tn args)   = TyDataRefined loc rep pknd tn (replaceNominal p n t <$> args)
  replaceNominal p n t (TyCodataRefined loc rep pknd tn args) = TyCodataRefined loc rep pknd tn (replaceNominal p n t <$> args)
  replaceNominal p n t (TyNominal loc rep pk t')         = if t == t'
                                                           then case rep of { PosRep -> p; NegRep -> n }
                                                           else TyNominal loc rep pk t' 
  replaceNominal p n t (TyApp loc rep ty args)           = TyApp loc rep (replaceNominal p n t ty) (replaceNominal p n t <$> args)
  replaceNominal p n t (TySyn loc rep tn ty)             = TySyn loc rep tn (replaceNominal p n t ty)
  replaceNominal _ _ _ ty@TyTop {}                       = ty
  replaceNominal _ _ _ ty@TyBot {}                       = ty
  replaceNominal p n t (TyUnion loc t1 t2)               = TyUnion loc (replaceNominal p n t t1) (replaceNominal p n t t2)
  replaceNominal p n t (TyInter loc t1 t2)               = TyInter loc (replaceNominal p n t t1) (replaceNominal p n t t2)
  replaceNominal p n t (TyRec loc rep var ty)            = TyRec loc rep var (replaceNominal p n t ty)
  replaceNominal _ _ _ ty@TyI64 {}                       = ty
  replaceNominal _ _ _ ty@TyF64 {}                       = ty
  replaceNominal _ _ _ ty@TyChar {}                      = ty
  replaceNominal _ _ _ ty@TyString {}                    = ty
  replaceNominal p n t (TyFlipPol rep ty)                = TyFlipPol rep (replaceNominal p n t ty)
  replaceNominal p n t (TyKindAnnot mk ty)               = TyKindAnnot mk (replaceNominal p n t ty)

instance ReplaceNominal (XtorSig pol) where
  replaceNominal :: forall pol. Typ Pos -> Typ Neg -> RnTypeName -> XtorSig pol -> XtorSig pol
  replaceNominal p n t MkXtorSig { sig_name, sig_args } =
    MkXtorSig { sig_name = sig_name, sig_args = replaceNominal p n t <$> sig_args }

instance ReplaceNominal (PrdCnsType pol) where
  replaceNominal :: forall pol. Typ Pos -> Typ Neg -> RnTypeName -> PrdCnsType pol -> PrdCnsType pol
  replaceNominal p n t (PrdCnsType rep ty) = PrdCnsType rep (replaceNominal p n t ty)

instance ReplaceNominal (VariantType pol) where
  replaceNominal :: forall pol. Typ Pos -> Typ Neg -> RnTypeName -> VariantType pol -> VariantType pol
  replaceNominal p n t (CovariantType ty)     = CovariantType (replaceNominal p n t ty)
  replaceNominal p n t (ContravariantType ty) = ContravariantType (replaceNominal p n t ty)

------------------------------------------------------------------------------
-- Type Schemes
------------------------------------------------------------------------------

data TypeScheme (pol :: Polarity) = TypeScheme
  { ts_loc :: Loc
  , ts_vars :: [MaybeKindedSkolem]
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
  freeTVars :: a -> Set SkolemTVar

instance FreeTVars (Typ pol) where
  freeTVars (TySkolemVar _  _ tv)        = S.singleton tv
  freeTVars TyRecVar{}                    = S.empty
  freeTVars TyUniVar{}                    = S.empty
  freeTVars TyTop {}                      = S.empty
  freeTVars TyBot {}                      = S.empty
  freeTVars (TyUnion _ ty ty')            = S.union (freeTVars ty) (freeTVars ty')
  freeTVars (TyInter _ ty ty')            = S.union (freeTVars ty) (freeTVars ty')
  freeTVars (TyRec _ _ _ t)               = freeTVars t
  freeTVars TyNominal{}                   = S.empty 
  freeTVars (TyApp _ _ ty args)     = S.union (freeTVars ty) (foldr S.union S.empty  (freeTVars <$> args))
  freeTVars (TySyn _ _ _ ty)              = freeTVars ty
  freeTVars (TyData _ _ xtors)            = S.unions (freeTVars <$> xtors)
  freeTVars (TyCodata _ _ xtors)          = S.unions (freeTVars <$> xtors)
  freeTVars (TyDataRefined _ _ _ _ xtors)   = S.unions (freeTVars <$> xtors)
  freeTVars (TyCodataRefined _ _ _ _ xtors) = S.unions (freeTVars <$> xtors)
  freeTVars (TyI64 _ _)                   = S.empty
  freeTVars (TyF64 _ _)                   = S.empty
  freeTVars (TyChar _ _)                  = S.empty
  freeTVars (TyString _ _)                = S.empty
  freeTVars (TyFlipPol _ ty)              = freeTVars ty
  freeTVars (TyKindAnnot _ ty)            = freeTVars ty


instance FreeTVars (PrdCnsType pol) where
  freeTVars (PrdCnsType _ ty) = freeTVars ty

instance FreeTVars (VariantType pol) where
  freeTVars (CovariantType ty)     = freeTVars ty
  freeTVars (ContravariantType ty) = freeTVars ty

instance FreeTVars (LinearContext pol) where
  freeTVars ctxt = S.unions (freeTVars <$> ctxt)

instance FreeTVars (XtorSig pol) where
  freeTVars MkXtorSig { sig_args } = freeTVars sig_args

-- | Generalize over all free type variables of a type.
generalize :: Typ pol -> TypeScheme pol
generalize ty = TypeScheme defaultLoc (zip (S.toList $ freeTVars ty) (repeat Nothing)) ty










