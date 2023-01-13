module Syntax.TST.Types where

import Data.Set (Set)
import Data.Set qualified as S
import Data.Map (Map)
import Data.Map qualified as M
import Data.List.NonEmpty (NonEmpty)
import Data.Maybe (fromMaybe)
import Data.Kind ( Type )
import Syntax.RST.Types (Polarity(..), PolarityRep(..), FlipPol ,PrdCnsFlip)
import Syntax.CST.Kinds
import Syntax.CST.Types ( PrdCnsRep(..), PrdCns(..), Arity)
import Syntax.CST.Names ( MethodName, RecTVar, RnTypeName, SkolemTVar, UniTVar, XtorName )

import Loc

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
  TySkolemVar     :: Loc -> PolarityRep pol -> PolyKind -> SkolemTVar -> Typ pol
  TyUniVar        :: Loc -> PolarityRep pol -> PolyKind -> UniTVar -> Typ pol
  TyRecVar        :: Loc -> PolarityRep pol -> PolyKind -> RecTVar -> Typ pol
  -- | We have to duplicate TyStructData and TyStructCodata here due to restrictions of the deriving mechanism of Haskell.
  -- | Refinement types are represented by the presence of the TypeName parameter
  TyData          :: Loc -> PolarityRep pol -> MonoKind                  -> [XtorSig pol]           -> Typ pol
  TyCodata        :: Loc -> PolarityRep pol -> MonoKind                  -> [XtorSig (FlipPol pol)] -> Typ pol
  TyDataRefined   :: Loc -> PolarityRep pol -> PolyKind   -> RnTypeName  -> [XtorSig pol]           -> Typ pol
  TyCodataRefined :: Loc -> PolarityRep pol -> PolyKind   -> RnTypeName  -> [XtorSig (FlipPol pol)] -> Typ pol
  -- | Nominal types with arguments to type parameters (contravariant, covariant)
  TyNominal       :: Loc -> PolarityRep pol -> PolyKind -> RnTypeName -> Typ pol
  TyApp           :: Loc -> PolarityRep pol -> Typ pol -> NonEmpty (VariantType pol) -> Typ pol
  -- | Type synonym
  TySyn           :: Loc -> PolarityRep pol -> RnTypeName -> Typ pol -> Typ pol
  -- | Lattice types
  TyBot           :: Loc -> PolyKind -> Typ Pos
  TyTop           :: Loc -> PolyKind -> Typ Neg
  TyUnion         :: Loc -> PolyKind -> Typ Pos -> Typ Pos -> Typ Pos
  TyInter         :: Loc -> PolyKind -> Typ Neg -> Typ Neg -> Typ Neg
  -- | Equirecursive Types
  TyRec           :: Loc -> PolarityRep pol -> RecTVar -> Typ pol -> Typ pol
  -- | Builtin Types
  TyI64           :: Loc -> PolarityRep pol -> Typ pol
  TyF64           :: Loc -> PolarityRep pol -> Typ pol
  TyChar          :: Loc -> PolarityRep pol -> Typ pol
  TyString        :: Loc -> PolarityRep pol -> Typ pol
  -- | TyFlipPol is only generated during focusing, and cannot be parsed!
  TyFlipPol       :: PolarityRep pol -> Typ (FlipPol pol) -> Typ pol

deriving instance Eq (Typ pol)
deriving instance Ord (Typ pol)
deriving instance Show (Typ pol)

mkUnion :: Loc -> PolyKind -> [Typ Pos] -> Typ Pos
mkUnion loc knd   []     = TyBot loc knd
mkUnion _   _   [t]    = t
mkUnion loc knd (t:ts) = TyUnion loc knd t (mkUnion loc knd ts)

mkInter :: Loc -> PolyKind -> [Typ Neg] -> Typ Neg
mkInter loc knd   []     = TyTop loc knd
mkInter _   _   [t]    = t
mkInter loc knd (t:ts) = TyInter loc knd t (mkInter loc knd ts)

getPolarity :: Typ pol -> PolarityRep pol
getPolarity (TySkolemVar _ rep _ _)        = rep
getPolarity (TyUniVar _ rep _ _)           = rep
getPolarity (TyRecVar _ rep _ _)           = rep
getPolarity (TyData _ rep _  _)            = rep
getPolarity (TyCodata _ rep _  _)          = rep
getPolarity (TyDataRefined _ rep  _ _ _)   = rep
getPolarity (TyCodataRefined _ rep  _ _ _) = rep
getPolarity (TyNominal _ rep _ _)          = rep
getPolarity (TyApp _ rep _ _)              = rep
getPolarity (TySyn _ rep _ _)              = rep
getPolarity TyTop {}                       = NegRep
getPolarity TyBot {}                       = PosRep
getPolarity TyUnion {}                     = PosRep
getPolarity TyInter {}                     = NegRep
getPolarity (TyRec _ rep _ _)              = rep
getPolarity (TyI64 _ rep)                  = rep
getPolarity (TyF64 _ rep)                  = rep
getPolarity (TyChar _ rep)                 = rep
getPolarity (TyString _ rep)               = rep
getPolarity (TyFlipPol rep _)              = rep


class GetMonoKind (a :: Type) where
  getMonoKind :: a -> MonoKind

instance GetMonoKind PolyKind where 
  getMonoKind (MkPolyKind _ eo) = CBox eo
  getMonoKind (KindVar kv) = MKindVar kv

instance GetMonoKind (Typ pol) where 
  getMonoKind (TySkolemVar _ _ pk _)        = getMonoKind pk
  getMonoKind (TyUniVar _ _ pk _)           = getMonoKind pk
  getMonoKind (TyRecVar _ _ pk _)           = getMonoKind pk 
  getMonoKind (TyData _ _ mk _ )            = mk
  getMonoKind (TyCodata _ _ mk _ )          = mk
  getMonoKind (TyDataRefined _ _ pk _ _ )   = getMonoKind pk 
  getMonoKind (TyCodataRefined _ _ pk _ _ ) = getMonoKind pk
  getMonoKind (TyNominal _ _ pk _ )         = getMonoKind pk
  getMonoKind (TyApp _ _ ty _)              = getMonoKind ty
  getMonoKind (TySyn _ _ _ ty)              = getMonoKind ty
  getMonoKind (TyTop _ pk)                  = getMonoKind pk
  getMonoKind (TyBot _ pk)                  = getMonoKind pk
  getMonoKind (TyUnion _ pk _ _)            = getMonoKind pk
  getMonoKind (TyInter _ pk _ _)            = getMonoKind pk
  getMonoKind (TyRec _ _ _ ty)              = getMonoKind ty
  getMonoKind TyI64{}                       = I64Rep
  getMonoKind TyF64{}                       = F64Rep
  getMonoKind TyChar{}                      = CharRep
  getMonoKind TyString{}                    = StringRep
  getMonoKind (TyFlipPol _ ty)              = getMonoKind ty

instance GetMonoKind (PrdCnsType pol) where 
  getMonoKind (PrdCnsType _ ty) = getMonoKind ty

instance GetMonoKind (VariantType pol) where 
  getMonoKind (CovariantType ty) = getMonoKind ty 
  getMonoKind (ContravariantType ty) = getMonoKind ty

class GetPolyKind (a :: Type) where 
  getPolyKind :: a -> Maybe PolyKind

instance GetPolyKind (Typ pol) where 
  getPolyKind (TySkolemVar _ _ pk _)        = Just pk
  getPolyKind (TyUniVar _ _ pk _)           = Just pk
  getPolyKind (TyRecVar _ _ pk _)           = Just pk 
  getPolyKind (TyDataRefined _ _ pk _ _ )   = Just pk
  getPolyKind (TyCodataRefined _ _ pk _ _ ) = Just pk 
  getPolyKind (TyNominal _ _ pk _ )         = Just pk 
  getPolyKind (TyApp _ _ ty _)              = getPolyKind ty 
  getPolyKind (TySyn _ _ _ ty)              = getPolyKind ty
  getPolyKind (TyTop _ pk)                  = Just pk
  getPolyKind (TyBot _ pk)                  = Just pk
  getPolyKind (TyUnion _ pk _ _)            = Just pk
  getPolyKind (TyInter _ pk _ _)            = Just pk
  getPolyKind (TyRec _ _ _ ty)              = getPolyKind ty
  getPolyKind (TyFlipPol _ ty)              = getPolyKind ty
  getPolyKind ty                            = case getMonoKind ty of 
    CBox eo -> Just $ MkPolyKind [] eo
    MKindVar kv -> Just $ KindVar kv
    _ -> Nothing

instance GetPolyKind (PrdCnsType pol) where 
  getPolyKind (PrdCnsType _ ty) = getPolyKind ty

instance GetPolyKind (VariantType pol) where 
  getPolyKind (CovariantType ty) = getPolyKind ty 
  getPolyKind (ContravariantType ty) = getPolyKind ty



------------------------------------------------------------------------------
-- Type Schemes
------------------------------------------------------------------------------

data TypeScheme (pol :: Polarity) = TypeScheme
  { ts_loc :: Loc
  , ts_vars :: [KindedSkolem]
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
  freeTVars :: a -> Set (SkolemTVar, PolyKind)

instance FreeTVars (Typ pol) where
  freeTVars (TySkolemVar _ _ knd tv)         = S.singleton (tv,knd)
  freeTVars TyRecVar{}                       = S.empty
  freeTVars TyUniVar{}                       = S.empty
  freeTVars TyTop {}                         = S.empty
  freeTVars TyBot {}                         = S.empty
  freeTVars (TyUnion _ _ ty ty')             = S.union (freeTVars ty) (freeTVars ty')
  freeTVars (TyInter _ _ ty ty')             = S.union (freeTVars ty) (freeTVars ty')
  freeTVars (TyRec _ _ _ t)                  = freeTVars t
  freeTVars TyNominal{}                      = S.empty
  freeTVars (TyApp _ _ ty args)              = S.union (freeTVars ty) (S.unions (freeTVars <$> args))
  freeTVars (TySyn _ _ _ ty)                 = freeTVars ty
  freeTVars (TyData _  _ _ xtors)            = S.unions (freeTVars <$> xtors)
  freeTVars (TyCodata _ _ _ xtors)           = S.unions (freeTVars <$> xtors)
  freeTVars (TyDataRefined _ _ _ _ xtors)    = S.unions (freeTVars <$> xtors)
  freeTVars (TyCodataRefined  _ _ _ _ xtors) = S.unions (freeTVars <$> xtors)
  freeTVars (TyI64 _ _)                      = S.empty
  freeTVars (TyF64 _ _)                      = S.empty
  freeTVars (TyChar _ _)                     = S.empty
  freeTVars (TyString _ _)                   = S.empty
  freeTVars (TyFlipPol _ ty)                 = freeTVars ty

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
generalize ty = TypeScheme defaultLoc (S.toList $ freeTVars ty) ty

------------------------------------------------------------------------------
-- Bisubstitution and Zonking
------------------------------------------------------------------------------

data VarType
  = UniVT
  | SkolemVT
  | RecVT

type family BisubstMap (vt :: VarType) :: Type where
  BisubstMap UniVT    = (Map UniTVar (Typ Pos, Typ Neg), Map KVar PolyKind, Map KVar MonoKind)
  BisubstMap SkolemVT = Map SkolemTVar (Typ Pos, Typ Neg)
  BisubstMap RecVT    = Map RecTVar (Typ Pos, Typ Neg)

getUVMap :: BisubstMap UniVT -> Map UniTVar (Typ Pos, Typ Neg)
getUVMap (m,_,_) = m

getKVMapPk :: BisubstMap UniVT -> Map KVar PolyKind
getKVMapPk (_,m,_) = m

getKVMapMk :: BisubstMap UniVT -> Map KVar MonoKind
getKVMapMk (_,_,m) = m


newtype Bisubstitution vt = MkBisubstitution { bisubst_map :: BisubstMap vt }

data VarTypeRep (vt :: VarType) where
  UniRep    :: VarTypeRep UniVT
  SkolemRep :: VarTypeRep SkolemVT
  RecRep    :: VarTypeRep RecVT

-- | Class of types for which a Bisubstitution can be applied.
class Zonk (a :: Type) where
  zonk :: VarTypeRep vt -> Bisubstitution vt -> a -> a

instance Zonk (Typ pol) where
  zonk UniRep bisubst ty@(TyUniVar _ PosRep _ tv) = 
    let zonkFun x = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) x in
    case M.lookup tv (getUVMap (bisubst_map bisubst)) of
      Nothing -> zonkFun ty
      Just (tyPos,_) -> zonkFun tyPos
  zonk UniRep bisubst ty@(TyUniVar _ NegRep _ tv) = 
    let zonkFun x = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) x in
    case M.lookup tv (getUVMap (bisubst_map bisubst)) of
      Nothing -> zonkFun ty 
      Just (_,tyNeg) -> zonkFun tyNeg 
  zonk SkolemRep _ ty@TyUniVar{} = ty
  zonk RecRep _ ty@TyUniVar{} = ty
  zonk UniRep bisubst ty@TySkolemVar{} = zonkMonoKind (getKVMapMk $ bisubst_map bisubst)  $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) ty
  zonk SkolemRep bisubst ty@(TySkolemVar _ PosRep _ tv) = case M.lookup tv (bisubst_map bisubst) of
     Nothing -> ty -- Recursive variable!
     Just (tyPos,_) -> tyPos
  zonk SkolemRep bisubst ty@(TySkolemVar _ NegRep _ tv) = case M.lookup tv (bisubst_map bisubst) of
     Nothing -> ty -- Recursive variable!
     Just (_,tyNeg) -> tyNeg
  zonk RecRep _ ty@TySkolemVar{} = ty
  zonk UniRep bisubst ty@TyRecVar{} = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) ty
  zonk SkolemRep _ ty@TyRecVar{} = ty
  zonk RecRep bisubst ty@(TyRecVar _ PosRep _ tv) = case M.lookup tv (bisubst_map bisubst) of
    Nothing -> ty
    Just (tyPos,_) -> tyPos
  zonk RecRep bisubst ty@(TyRecVar _ NegRep _ tv) = case M.lookup tv (bisubst_map bisubst) of
    Nothing -> ty
    Just (_,tyNeg) -> tyNeg
  zonk UniRep bisubst (TyData loc rep mk xtors) =
     let knd = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) mk in
     TyData loc rep knd (zonk UniRep bisubst <$> xtors)
  zonk vt bisubst (TyData loc rep mk xtors) =
     TyData loc rep  mk (zonk vt bisubst <$> xtors)
  zonk UniRep bisubst (TyCodata loc rep mk xtors) =
     let knd = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) mk in
     TyCodata loc rep knd (zonk UniRep bisubst <$> xtors)
  zonk vt bisubst (TyCodata loc rep mk xtors) =
     TyCodata loc rep mk (zonk vt bisubst <$> xtors)
  zonk UniRep bisubst (TyDataRefined loc rep pk tn xtors) =
     let knd = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) pk in
     TyDataRefined loc rep knd tn (zonk UniRep bisubst <$> xtors)
  zonk vt bisubst (TyDataRefined loc rep pk tn xtors) =
     TyDataRefined loc rep pk tn (zonk vt bisubst <$> xtors)
  zonk UniRep bisubst (TyCodataRefined loc rep pk tn xtors) =
     let knd = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) pk in
     TyCodataRefined loc rep knd tn (zonk UniRep bisubst <$> xtors)
  zonk vt bisubst (TyCodataRefined loc rep pk tn xtors) =
     TyCodataRefined loc rep pk tn (zonk vt bisubst <$> xtors)
  zonk UniRep bisubst (TyNominal loc rep pk tn) = 
    let knd = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) pk in
    TyNominal loc rep knd tn 
  zonk _ _ (TyNominal loc rep kind tn) =
     TyNominal loc rep kind tn 
  zonk vt bisubst (TyApp loc rep ty args) = 
    TyApp loc rep (zonk vt bisubst ty) (zonk vt bisubst <$> args)
  zonk vt bisubst (TySyn loc rep nm ty) =
     TySyn loc rep nm (zonk vt bisubst ty)
  zonk UniRep bisubst (TyTop loc pk) = 
    let knd = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) pk in
    TyTop loc knd
  zonk _vt _ (TyTop loc mk) =
    TyTop loc mk
  zonk UniRep bisubst (TyBot loc pk) = 
    let knd = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) pk in
    TyBot loc knd
  zonk _vt _ (TyBot loc pk) =
    TyBot loc pk
  zonk UniRep bisubst (TyUnion loc pk ty1 ty2) = 
    let knd = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) pk in
    TyUnion loc knd (zonk UniRep bisubst ty1) (zonk UniRep bisubst ty2)
  zonk vt bisubst (TyUnion loc pknd ty ty') =
    TyUnion loc pknd (zonk vt bisubst ty) (zonk vt bisubst ty')
  zonk UniRep bisubst (TyInter loc pk ty1 ty2) = 
    let knd = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) pk in
    TyInter loc knd (zonk UniRep bisubst ty1) (zonk UniRep bisubst ty2)
  zonk vt bisubst (TyInter loc pknd ty ty') =
    TyInter loc pknd (zonk vt bisubst ty) (zonk vt bisubst ty')
  zonk RecRep bisubst (TyRec loc rep tv ty) =
    let bisubst' = MkBisubstitution $ M.delete tv (bisubst_map bisubst)
    in TyRec loc rep tv $ zonk RecRep bisubst' ty
  zonk vt bisubst (TyRec loc rep tv ty) =
     TyRec loc rep tv (zonk vt bisubst ty)
  zonk _vt _ t@TyI64 {} = t
  zonk _vt _ t@TyF64 {} = t
  zonk _vt _ t@TyChar {} = t
  zonk _vt _ t@TyString {} = t
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

instance Zonk (TypeScheme pol) where 
  zonk UniRep bisubst (TypeScheme {ts_loc = loc, ts_vars = tvars, ts_monotype = ty}) =
    let zonkFun x = zonkMonoKind (getKVMapMk $ bisubst_map bisubst) $ zonkPolyKind (getKVMapPk $ bisubst_map bisubst) x in
    TypeScheme {ts_loc = loc, ts_vars = map zonkFun tvars, ts_monotype = zonk UniRep bisubst ty}
  zonk _ _ _ = error "Not implemented"

class ZonkKind (a::Type) where 
  zonkMonoKind :: Map KVar MonoKind -> a -> a
  zonkPolyKind :: Map KVar PolyKind -> a -> a

instance ZonkKind MonoKind where 
  zonkMonoKind bisubst kindV@(MKindVar kv) = Data.Maybe.fromMaybe kindV (M.lookup kv bisubst)
  zonkMonoKind _ (CBox cc) = CBox cc
  zonkMonoKind _ F64Rep = F64Rep 
  zonkMonoKind _ I64Rep = I64Rep
  zonkMonoKind _ CharRep = CharRep
  zonkMonoKind _ StringRep = StringRep
  zonkPolyKind _ mk = mk

instance ZonkKind PolyKind where 
  zonkMonoKind bisubst (MkPolyKind args eval) = 
    MkPolyKind (map (\(x,y,z) -> (x,y, zonkMonoKind bisubst z)) args) eval 
  zonkMonoKind _ kindV@(KindVar _) = kindV
  zonkPolyKind bisubst kindV@(KindVar kv) = Data.Maybe.fromMaybe kindV (M.lookup kv bisubst)
  zonkPolyKind _ pk@(MkPolyKind _ _) = pk


instance ZonkKind (Typ pol) where 
  zonkMonoKind bisubst (TySkolemVar loc rep mk tv) = 
    TySkolemVar loc rep (zonkMonoKind bisubst mk) tv 
  zonkMonoKind bisubst (TyUniVar loc rep mk tv) = 
    TyUniVar loc rep (zonkMonoKind bisubst mk) tv 
  zonkMonoKind bisubst (TyRecVar loc rep mk tv) = 
    TyRecVar loc rep (zonkMonoKind bisubst mk) tv
  zonkMonoKind bisubst (TyData loc pol mk xtors) = 
    TyData loc pol (zonkMonoKind bisubst mk) (zonkMonoKind bisubst <$> xtors)
  zonkMonoKind bisubst (TyCodata loc pol mk xtors) = 
    TyCodata loc pol (zonkMonoKind bisubst mk) (zonkMonoKind bisubst <$> xtors)
  zonkMonoKind bisubst (TyDataRefined loc pol pk tyn xtors) = 
    TyDataRefined loc pol (zonkMonoKind bisubst pk) tyn (zonkMonoKind bisubst <$> xtors)
  zonkMonoKind bisubst (TyCodataRefined loc pol pk tyn xtors) = 
    TyCodataRefined loc pol (zonkMonoKind bisubst pk) tyn (zonkMonoKind bisubst <$> xtors)
  zonkMonoKind bisubst (TyNominal loc pol pk tyn) = 
    TyNominal loc pol (zonkMonoKind bisubst pk) tyn 
  zonkMonoKind bisubst (TyApp loc pol ty args) = 
    TyApp loc pol (zonkMonoKind bisubst ty) (zonkMonoKind bisubst <$> args)
  zonkMonoKind bisubst (TySyn loc pol tyn ty) = 
    TySyn loc pol tyn (zonkMonoKind bisubst ty)
  zonkMonoKind bisubst (TyTop loc pk) = 
    TyTop loc (zonkMonoKind bisubst pk)
  zonkMonoKind bisubst (TyBot loc pk) = 
    TyBot loc (zonkMonoKind bisubst pk)
  zonkMonoKind bisubst (TyUnion loc pk ty1 ty2) = 
    TyUnion loc (zonkMonoKind bisubst pk) (zonkMonoKind bisubst ty1) (zonkMonoKind bisubst ty2)
  zonkMonoKind bisubst (TyInter loc pk ty1 ty2) = 
    TyInter loc (zonkMonoKind bisubst pk) (zonkMonoKind bisubst ty1) (zonkMonoKind bisubst ty2)
  zonkMonoKind bisubst (TyRec loc pol rv ty) = 
    TyRec loc pol rv (zonkMonoKind bisubst ty)
  zonkMonoKind _ ty@TyI64{} = ty
  zonkMonoKind _ ty@TyF64{} = ty
  zonkMonoKind _ ty@TyChar{} = ty
  zonkMonoKind _ ty@TyString{} = ty
  zonkMonoKind bisubst (TyFlipPol pol ty) = TyFlipPol pol (zonkMonoKind bisubst ty)

  zonkPolyKind bisubst (TySkolemVar loc rep mk tv) = 
    TySkolemVar loc rep (zonkPolyKind bisubst mk) tv 
  zonkPolyKind bisubst (TyUniVar loc rep mk tv) = 
    TyUniVar loc rep (zonkPolyKind bisubst mk) tv 
  zonkPolyKind bisubst (TyRecVar loc rep mk tv) = 
    TyRecVar loc rep (zonkPolyKind bisubst mk) tv
  zonkPolyKind bisubst (TyData loc pol mk xtors) = 
    TyData loc pol (zonkPolyKind bisubst mk) (zonkPolyKind bisubst <$> xtors)
  zonkPolyKind bisubst (TyCodata loc pol mk xtors) = 
    TyCodata loc pol (zonkPolyKind bisubst mk) (zonkPolyKind bisubst <$> xtors)
  zonkPolyKind bisubst (TyDataRefined loc pol pk tyn xtors) = 
    TyDataRefined loc pol (zonkPolyKind bisubst pk) tyn (zonkPolyKind bisubst <$> xtors)
  zonkPolyKind bisubst (TyCodataRefined loc pol pk tyn xtors) = 
    TyCodataRefined loc pol (zonkPolyKind bisubst pk) tyn (zonkPolyKind bisubst <$> xtors)
  zonkPolyKind bisubst (TyNominal loc pol pk tyn) = 
    TyNominal loc pol (zonkPolyKind bisubst pk) tyn 
  zonkPolyKind bisubst (TyApp loc pol ty args) = 
    TyApp loc pol (zonkPolyKind bisubst ty) (zonkPolyKind bisubst <$> args)
  zonkPolyKind bisubst (TySyn loc pol tyn ty) = 
    TySyn loc pol tyn (zonkPolyKind bisubst ty)
  zonkPolyKind bisubst (TyTop loc pk) = 
    TyTop loc (zonkPolyKind bisubst pk)
  zonkPolyKind bisubst (TyBot loc pk) = 
    TyBot loc (zonkPolyKind bisubst pk)
  zonkPolyKind bisubst (TyUnion loc pk ty1 ty2) = 
    TyUnion loc (zonkPolyKind bisubst pk) (zonkPolyKind bisubst ty1) (zonkPolyKind bisubst ty2)
  zonkPolyKind bisubst (TyInter loc pk ty1 ty2) = 
    TyInter loc (zonkPolyKind bisubst pk) (zonkPolyKind bisubst ty1) (zonkPolyKind bisubst ty2)
  zonkPolyKind bisubst (TyRec loc pol rv ty) = 
    TyRec loc pol rv (zonkPolyKind bisubst ty)
  zonkPolyKind _ ty@TyI64{} = ty
  zonkPolyKind _ ty@TyF64{} = ty
  zonkPolyKind _ ty@TyChar{} = ty
  zonkPolyKind _ ty@TyString{} = ty
  zonkPolyKind bisubst (TyFlipPol pol ty) = TyFlipPol pol (zonkPolyKind bisubst ty)



instance ZonkKind (XtorSig pol) where 
  zonkMonoKind bisubst (MkXtorSig { sig_name = nm, sig_args = args }) = 
    MkXtorSig {sig_name = nm, sig_args = zonkMonoKind bisubst <$> args}
  zonkPolyKind bisubst (MkXtorSig { sig_name = nm, sig_args = args }) = 
    MkXtorSig {sig_name = nm, sig_args = zonkPolyKind bisubst <$> args}
 
instance ZonkKind (LinearContext pol) where 
  zonkMonoKind bisubst = map (zonkMonoKind bisubst)
  zonkPolyKind bisubst = map (zonkPolyKind bisubst)

instance ZonkKind (PrdCnsType pol) where 
  zonkMonoKind bisubst (PrdCnsType rep ty) = PrdCnsType rep (zonkMonoKind bisubst ty)
  zonkPolyKind bisubst (PrdCnsType rep ty) = PrdCnsType rep (zonkPolyKind bisubst ty)


instance ZonkKind (VariantType pol) where 
  zonkMonoKind bisubst (CovariantType ty) = CovariantType (zonkMonoKind bisubst ty)
  zonkMonoKind bisubst (ContravariantType ty) = ContravariantType (zonkMonoKind bisubst ty)
  zonkPolyKind bisubst (CovariantType ty) = CovariantType (zonkPolyKind bisubst ty)
  zonkPolyKind bisubst (ContravariantType ty) = ContravariantType (zonkPolyKind bisubst ty)

instance ZonkKind KindedSkolem where 
  zonkMonoKind bisubst (sk,mk) = (sk, zonkMonoKind bisubst mk)
  zonkPolyKind bisubst (sk,mk) = (sk, zonkPolyKind bisubst mk)

-- This is probably not 100% correct w.r.t alpha-renaming. Postponed until we have a better repr. of types.
unfoldRecType :: Typ pol -> Typ pol
unfoldRecType recty@(TyRec _ PosRep var ty) = zonk RecRep (MkBisubstitution (M.fromList [(var,(recty, error "unfoldRecType"))])) ty
unfoldRecType recty@(TyRec _ NegRep var ty) = zonk RecRep (MkBisubstitution (M.fromList [(var,(error "unfoldRecType", recty))])) ty
unfoldRecType ty = ty
