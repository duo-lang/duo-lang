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

data MethodSig (pol :: Polarity) = MkMethodSig
  { msig_name :: MethodName
  , msig_args :: [PrdCnsType pol]
  }

deriving instance Eq (MethodSig pol)
deriving instance Ord (MethodSig pol)
deriving instance Show (MethodSig pol)


data Typ (pol :: Polarity) where
  TySkolemVar :: Loc -> PolarityRep pol -> Maybe MonoKind -> SkolemTVar -> Typ pol
  TyUniVar :: Loc -> PolarityRep pol -> Maybe MonoKind -> UniTVar -> Typ pol
  -- | We have to duplicate TyStructData and TyStructCodata here due to restrictions of the deriving mechanism of Haskell.
  -- | Refinement types are represented by the presence of the TypeName parameter
  TyData          :: Loc -> PolarityRep pol               -> [XtorSig pol]           -> Typ pol
  TyCodata        :: Loc -> PolarityRep pol               -> [XtorSig (FlipPol pol)] -> Typ pol
  TyDataRefined   :: Loc -> PolarityRep pol -> RnTypeName -> [XtorSig pol]           -> Typ pol
  TyCodataRefined :: Loc -> PolarityRep pol -> RnTypeName -> [XtorSig (FlipPol pol)] -> Typ pol
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
  TyRec :: Loc -> PolarityRep pol -> SkolemTVar -> Typ pol -> Typ pol
  -- | Builtin Types
  TyI64 :: Loc -> PolarityRep pol -> Typ pol
  TyF64 :: Loc -> PolarityRep pol -> Typ pol
  -- | TyFlipPol is only generated during focusing, and cannot be parsed!
  TyFlipPol :: PolarityRep pol -> Typ (FlipPol pol) -> Typ pol

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
getPolarity (TySkolemVar _ rep _ _)     = rep
getPolarity (TyUniVar _ rep _ _)        = rep
getPolarity (TyData _ rep _)            = rep
getPolarity (TyCodata _ rep _)          = rep
getPolarity (TyDataRefined _ rep _ _)   = rep
getPolarity (TyCodataRefined _ rep _ _) = rep
getPolarity (TyNominal _ rep _ _ _)     = rep
getPolarity (TySyn _ rep _ _)           = rep
getPolarity TyTop {}                    = NegRep
getPolarity TyBot {}                    = PosRep
getPolarity TyUnion {}                  = PosRep
getPolarity TyInter {}                  = NegRep
getPolarity (TyRec _ rep _ _)           = rep
getPolarity (TyI64 _ rep)               = rep
getPolarity (TyF64 _ rep)               = rep
getPolarity (TyFlipPol rep _)           = rep



------------------------------------------------------------------------------
-- Type Schemes
------------------------------------------------------------------------------

data TypeScheme (pol :: Polarity) = TypeScheme
  { ts_loc :: Loc
  , ts_vars :: [SkolemTVar]
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
  freeTVars (TySkolemVar _ _ _ tv)        = S.singleton tv
  freeTVars TyUniVar{}                    = S.empty
  freeTVars TyTop {}                      = S.empty
  freeTVars TyBot {}                      = S.empty
  freeTVars (TyUnion _ _ ty ty')          = S.union (freeTVars ty) (freeTVars ty')
  freeTVars (TyInter _ _ ty ty')          = S.union (freeTVars ty) (freeTVars ty')
  freeTVars (TyRec _ _ tv t)              = S.delete tv $ freeTVars t
  freeTVars (TyNominal _ _ _ _ args)      = S.unions (freeTVars <$> args)
  freeTVars (TySyn _ _ _ ty)              = freeTVars ty
  freeTVars (TyData _ _ xtors)            = S.unions (freeTVars <$> xtors)
  freeTVars (TyCodata _ _ xtors)          = S.unions (freeTVars <$> xtors)
  freeTVars (TyDataRefined _ _ _ xtors)   = S.unions (freeTVars <$> xtors)
  freeTVars (TyCodataRefined _ _ _ xtors) = S.unions (freeTVars <$> xtors)
  freeTVars (TyI64 _ _)                   = S.empty
  freeTVars (TyF64 _ _)                   = S.empty
  freeTVars (TyFlipPol _ ty)              = freeTVars ty

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
generalize ty = TypeScheme defaultLoc (S.toList (freeTVars ty)) ty
------------------------------------------------------------------------------
-- Bisubstitution and Zonking
------------------------------------------------------------------------------

data VarType
  = UniVT
  | SkolemVT

type family BisubstMap (vt :: VarType) :: Type where
  BisubstMap UniVT    = Map UniTVar (Typ Pos, Typ Neg)
  BisubstMap SkolemVT = Map SkolemTVar (Typ Pos, Typ Neg)

newtype Bisubstitution vt = MkBisubstitution { bisubst_map :: BisubstMap vt }

data VarTypeRep (vt :: VarType) where
  UniRep    :: VarTypeRep UniVT
  SkolemRep :: VarTypeRep SkolemVT

-- | Class of types for which a Bisubstitution can be applied.
class Zonk (a :: Type) where
  zonk :: VarTypeRep vt -> Bisubstitution vt -> a -> a

instance Zonk (Typ pol) where
  zonk UniRep bisubst ty@(TyUniVar _ PosRep _ tv) = case M.lookup tv (bisubst_map bisubst) of
     Nothing -> ty -- Recursive variable!
     Just (tyPos,_) -> tyPos
  zonk SkolemRep _bisubst ty@(TyUniVar _ PosRep _ _) = ty
  zonk UniRep bisubst ty@(TyUniVar _ NegRep _ tv) = case M.lookup tv (bisubst_map bisubst) of
     Nothing -> ty -- Recursive variable!
     Just (_,tyNeg) -> tyNeg
  zonk SkolemRep _bisubst ty@(TyUniVar _ NegRep _ _) = ty
  zonk UniRep _bisubst ty@(TySkolemVar _ PosRep _ _) = ty
  zonk SkolemRep bisubst ty@(TySkolemVar _ PosRep _ tv) = case M.lookup tv (bisubst_map bisubst) of
     Nothing -> ty -- Recursive variable!
     Just (tyPos,_) -> tyPos
  zonk UniRep _bisubst ty@(TySkolemVar _ NegRep _ _v) = ty
  zonk SkolemRep bisubst ty@(TySkolemVar _ NegRep _ tv) = case M.lookup tv (bisubst_map bisubst) of
     Nothing -> ty -- Recursive variable!
     Just (_,tyNeg) -> tyNeg
  zonk vt bisubst (TyData loc rep xtors) =
     TyData loc rep (zonk vt bisubst <$> xtors)
  zonk vt bisubst (TyCodata loc rep xtors) =
     TyCodata loc rep (zonk vt bisubst <$> xtors)
  zonk vt bisubst (TyDataRefined loc rep tn xtors) =
     TyDataRefined loc rep tn (zonk vt bisubst <$> xtors)
  zonk vt bisubst (TyCodataRefined loc rep tn xtors) =
     TyCodataRefined loc rep tn (zonk vt bisubst <$> xtors)
  zonk vt bisubst (TyNominal loc rep kind tn args) =
     TyNominal loc rep kind tn (zonk vt bisubst <$> args)
  zonk vt bisubst (TySyn loc rep nm ty) =
     TySyn loc rep nm (zonk vt bisubst ty)
  zonk _vt _ (TyTop loc knd) =
    TyTop loc knd
  zonk _vt _ (TyBot loc knd) =
    TyBot loc knd
  zonk vt bisubst (TyUnion loc knd ty ty') =
    TyUnion loc knd (zonk vt bisubst ty) (zonk vt bisubst ty')
  zonk vt bisubst (TyInter loc knd ty ty') =
    TyInter loc knd (zonk vt bisubst ty) (zonk vt bisubst ty')
  zonk vt bisubst (TyRec loc rep tv ty) =
     TyRec loc rep tv (zonk vt bisubst ty)
  zonk _vt _ t@TyI64 {} = t
  zonk _vt _ t@TyF64 {} = t
  zonk vt bisubst (TyFlipPol rep ty) = TyFlipPol rep (zonk vt bisubst ty)

instance Zonk (VariantType pol) where
  zonk vt bisubst (CovariantType ty) = CovariantType (zonk vt bisubst ty)
  zonk vt bisubst (ContravariantType ty) = ContravariantType (zonk vt bisubst ty)

instance Zonk (XtorSig pol) where
  zonk vt bisubst (MkXtorSig name ctxt) =
    MkXtorSig name (zonk vt bisubst ctxt)

instance Zonk (LinearContext pol) where
  zonk vt bisubst = fmap (zonk vt bisubst)

instance Zonk (PrdCnsType pol) where
  zonk vt bisubst (PrdCnsType rep ty) = PrdCnsType rep (zonk vt bisubst ty)


-- This is probably not 100% correct w.r.t alpha-renaming. Postponed until we have a better repr. of types.
unfoldRecType :: Typ pol -> Typ pol
unfoldRecType recty@(TyRec _ PosRep var ty) = zonk SkolemRep (MkBisubstitution (M.fromList [(var,(recty, error "unfoldRecType"))])) ty
unfoldRecType recty@(TyRec _ NegRep var ty) = zonk SkolemRep (MkBisubstitution (M.fromList [(var,(error "unfoldRecType", recty))])) ty
unfoldRecType ty = ty

------------------------------------------------------------------------------
-- Data Type declarations
------------------------------------------------------------------------------

-- | A toplevel declaration of a data or codata type.
data DataDecl = NominalDecl
  { data_loc :: Loc
    -- ^ The source code location of the declaration.
  , data_doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , data_refined :: IsRefined
    -- ^ Whether an ordinary or a refinement type is declared.
  , data_name :: RnTypeName
    -- ^ The name of the type. E.g. "List".
  , data_polarity :: DataCodata
    -- ^ Whether a data or codata type is declared.
  , data_kind :: PolyKind
    -- ^ The kind of the type constructor.
  , data_xtors :: ([XtorSig Pos], [XtorSig Neg])
    -- The constructors/destructors of the declaration.
  }

deriving instance (Show DataDecl)
