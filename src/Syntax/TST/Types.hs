module Syntax.TST.Types where
import Data.Set (Set)
import Data.Set qualified as S
import Data.Map (Map)
import Data.Map qualified as M
import Data.List.NonEmpty (NonEmpty)
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
  TyUniVar        :: Loc -> PolarityRep pol -> AnyKind -> UniTVar -> Typ pol
  TyRecVar        :: Loc -> PolarityRep pol -> PolyKind -> RecTVar -> Typ pol
  -- | We have to duplicate TyStructData and TyStructCodata here due to restrictions of the deriving mechanism of Haskell.
  -- | Refinement types are represented by the presence of the TypeName parameter
  TyData          :: Loc -> PolarityRep pol -> EvaluationOrder           -> [XtorSig pol]           -> Typ pol
  TyCodata        :: Loc -> PolarityRep pol -> EvaluationOrder           -> [XtorSig (FlipPol pol)] -> Typ pol
  TyDataRefined   :: Loc -> PolarityRep pol -> PolyKind   -> RnTypeName  -> Maybe RecTVar -> [XtorSig pol]           -> Typ pol
  TyCodataRefined :: Loc -> PolarityRep pol -> PolyKind   -> RnTypeName  -> Maybe RecTVar -> [XtorSig (FlipPol pol)] -> Typ pol
  -- | Nominal types with arguments to type parameters (contravariant, covariant)
  TyNominal       :: Loc -> PolarityRep pol -> PolyKind -> RnTypeName -> Typ pol
  TyApp           :: Loc -> PolarityRep pol -> Typ pol -> NonEmpty (VariantType pol) -> Typ pol
  -- | Type synonym
  TySyn           :: Loc -> PolarityRep pol -> RnTypeName -> Typ pol -> Typ pol
  -- | Lattice types
  TyBot           :: Loc -> AnyKind -> Typ Pos
  TyTop           :: Loc -> AnyKind -> Typ Neg
  TyUnion         :: Loc -> AnyKind -> Typ Pos -> Typ Pos -> Typ Pos
  TyInter         :: Loc -> AnyKind -> Typ Neg -> Typ Neg -> Typ Neg
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

instance HasLoc (Typ pol) where 
  getLoc :: Typ pol -> Loc
  getLoc (TySkolemVar loc _ _ _)         = loc
  getLoc (TyUniVar loc _ _ _)            = loc
  getLoc (TyRecVar loc _ _ _)            = loc
  getLoc (TyData loc _ _ _ )             = loc
  getLoc (TyCodata loc _ _ _)            = loc
  getLoc (TyDataRefined loc _ _ _ _ _)   = loc
  getLoc (TyCodataRefined loc _ _ _ _ _) = loc
  getLoc (TyNominal loc _ _ _)           = loc
  getLoc (TyApp loc _ _ _)               = loc
  getLoc (TySyn loc _ _ _)               = loc
  getLoc (TyBot loc _)                   = loc
  getLoc (TyTop loc _)                   = loc
  getLoc (TyUnion loc _ _ _)             = loc 
  getLoc (TyInter loc _ _ _)             = loc
  getLoc (TyRec loc _ _ _)               = loc
  getLoc (TyI64 loc _)                   = loc
  getLoc (TyF64 loc _)                   = loc
  getLoc (TyChar loc _)                  = loc
  getLoc (TyString loc _)                = loc
  getLoc (TyFlipPol _ ty)                = getLoc ty


mkUnion :: Loc -> AnyKind -> [Typ Pos] -> Typ Pos
mkUnion loc knd   []     = TyBot loc knd
mkUnion _   _   [t]    = t
mkUnion loc knd (t:ts) = TyUnion loc knd t (mkUnion loc knd ts)

mkInter :: Loc -> AnyKind -> [Typ Neg] -> Typ Neg
mkInter loc knd   []     = TyTop loc knd
mkInter _   _   [t]    = t
mkInter loc knd (t:ts) = TyInter loc knd t (mkInter loc knd ts)

getPolarity :: Typ pol -> PolarityRep pol
getPolarity (TySkolemVar _ rep _ _)          = rep
getPolarity (TyUniVar _ rep _ _)             = rep
getPolarity (TyRecVar _ rep _ _)             = rep
getPolarity (TyData _ rep _  _)              = rep
getPolarity (TyCodata _ rep _  _)            = rep
getPolarity (TyDataRefined _ rep  _ _ _ _)   = rep
getPolarity (TyCodataRefined _ rep  _ _ _ _) = rep
getPolarity (TyNominal _ rep _ _)            = rep
getPolarity (TyApp _ rep _ _)                = rep
getPolarity (TySyn _ rep _ _)                = rep
getPolarity TyTop {}                         = NegRep
getPolarity TyBot {}                         = PosRep
getPolarity TyUnion {}                       = PosRep
getPolarity TyInter {}                       = NegRep
getPolarity (TyRec _ rep _ _)                = rep
getPolarity (TyI64 _ rep)                    = rep
getPolarity (TyF64 _ rep)                    = rep
getPolarity (TyChar _ rep)                   = rep
getPolarity (TyString _ rep)                 = rep
getPolarity (TyFlipPol rep _)                = rep

class GetKind (a :: Type) where 
  getKind :: a -> AnyKind

instance GetKind PolyKind where 
  getKind = MkPknd

instance GetKind (Typ pol) where 
  getKind (TySkolemVar _ _ pk _)          = MkPknd pk
  getKind (TyUniVar _ _ knd _)            = knd
  getKind (TyRecVar _ _ pk _)             = MkPknd pk 
  getKind (TyData _ _ eo _ )              = MkPknd $ MkPolyKind [] eo
  getKind (TyCodata _ _ eo _ )            = MkPknd $ MkPolyKind [] eo
  getKind (TyDataRefined _ _ pk _ _ _)    = MkPknd pk
  getKind (TyCodataRefined _ _ pk _ _ _)  = MkPknd pk
  getKind (TyNominal _ _ pk _ )           = MkPknd pk
  getKind (TyApp _ _ ty _)                = getKind ty
  getKind (TySyn _ _ _ ty)                = getKind ty
  getKind (TyTop _ knd)                   = knd
  getKind (TyBot _ knd)                   = knd
  getKind (TyUnion _ knd _ _)             = knd
  getKind (TyInter _ knd _ _)             = knd
  getKind (TyRec _ _ _ ty)                = getKind ty
  getKind TyI64{}                         = MkI64
  getKind TyF64{}                         = MkF64
  getKind TyChar{}                        = MkChar
  getKind TyString{}                      = MkString
  getKind (TyFlipPol _ ty)                = getKind ty

instance GetKind (PrdCnsType pol) where 
  getKind (PrdCnsType _ ty) = getKind ty

instance GetKind (VariantType pol) where 
  getKind (CovariantType ty) = getKind ty 
  getKind (ContravariantType ty) = getKind ty

-- | Typeclass for computing occurring recursive variables
class RecTVars (a :: Type) where
  recTVars :: a -> Set RecTVar

instance RecTVars (Typ pol) where
  recTVars TySkolemVar{}                        = S.empty
  recTVars (TyRecVar _ _ _ rv)                  = S.singleton rv
  recTVars TyUniVar{}                           = S.empty
  recTVars TyTop {}                             = S.empty
  recTVars TyBot {}                             = S.empty
  recTVars (TyUnion _ _ ty ty')                 = S.union (recTVars ty) (recTVars ty')
  recTVars (TyInter _ _ ty ty')                 = S.union (recTVars ty) (recTVars ty')
  recTVars (TyRec _ _ rv t)                     = S.union (S.singleton rv) (recTVars t)
  recTVars TyNominal{}                          = S.empty
  recTVars (TyApp _ _ ty args)                  = S.union (recTVars ty) (S.unions (recTVars <$> args))
  recTVars (TySyn _ _ _ ty)                     = recTVars ty
  recTVars (TyData _  _ _ xtors)                = S.unions (recTVars <$> xtors)
  recTVars (TyCodata _ _ _ xtors)               = S.unions (recTVars <$> xtors)
  recTVars (TyDataRefined _ _ _ _ mrv xtors)    = S.union (maybe S.empty S.singleton mrv) (S.unions (recTVars <$> xtors))
  recTVars (TyCodataRefined  _ _ _ _ mrv xtors) = S.union (maybe S.empty S.singleton mrv) (S.unions (recTVars <$> xtors))
  recTVars (TyI64 _ _)                          = S.empty
  recTVars (TyF64 _ _)                          = S.empty
  recTVars (TyChar _ _)                         = S.empty
  recTVars (TyString _ _)                       = S.empty
  recTVars (TyFlipPol _ ty)                     = recTVars ty

instance RecTVars (PrdCnsType pol) where
  recTVars (PrdCnsType _ ty) = recTVars ty

instance RecTVars (VariantType pol) where
  recTVars (CovariantType ty)     = recTVars ty
  recTVars (ContravariantType ty) = recTVars ty

instance RecTVars (LinearContext pol) where
  recTVars ctxt = S.unions (recTVars <$> ctxt)

instance RecTVars (XtorSig pol) where
  recTVars xtor = recTVars xtor.sig_args 

instance RecTVars [XtorSig pol] where 
  recTVars xtors = S.unions (recTVars <$> xtors)

-- used to get typename of application
getTypeNames :: Typ pol -> [RnTypeName]
getTypeNames TySkolemVar{} = []
getTypeNames TyUniVar{} = []
getTypeNames TyRecVar{} = []  
getTypeNames TyData{} = []
getTypeNames TyCodata{} = []
getTypeNames (TyDataRefined _ _ _ tyn _ _) = [tyn]
getTypeNames (TyCodataRefined _ _ _ tyn _ _) = [tyn]
getTypeNames (TyNominal _ _ _ tyn) = [tyn]
getTypeNames (TyApp _ _ ty _) = getTypeNames ty
getTypeNames (TySyn _ _ tyn _) = [tyn]
getTypeNames TyBot{} = []
getTypeNames TyTop{} = []
getTypeNames (TyUnion _ _ ty1 ty2) = getTypeNames ty1 ++ getTypeNames ty2
getTypeNames (TyInter _ _ ty1 ty2) = getTypeNames ty1 ++ getTypeNames ty2
getTypeNames TyRec{} = []
getTypeNames TyI64{} = []
getTypeNames TyF64{} = []
getTypeNames TyString{} = []
getTypeNames TyChar{} = [] 
getTypeNames (TyFlipPol _ ty) = getTypeNames ty

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
  freeTVars (TySkolemVar _ _ knd tv)           = S.singleton (tv,knd)
  freeTVars TyRecVar{}                         = S.empty
  freeTVars TyUniVar{}                         = S.empty
  freeTVars TyTop {}                           = S.empty
  freeTVars TyBot {}                           = S.empty
  freeTVars (TyUnion _ _ ty ty')               = S.union (freeTVars ty) (freeTVars ty')
  freeTVars (TyInter _ _ ty ty')               = S.union (freeTVars ty) (freeTVars ty')
  freeTVars (TyRec _ _ _ t)                    = freeTVars t
  freeTVars TyNominal{}                        = S.empty
  freeTVars (TyApp _ _ ty args)                = S.union (freeTVars ty) (S.unions (freeTVars <$> args))
  freeTVars (TySyn _ _ _ ty)                   = freeTVars ty
  freeTVars (TyData _  _ _ xtors)              = S.unions (freeTVars <$> xtors)
  freeTVars (TyCodata _ _ _ xtors)             = S.unions (freeTVars <$> xtors)
  freeTVars (TyDataRefined _ _ _ _ _ xtors)    = S.unions (freeTVars <$> xtors)
  freeTVars (TyCodataRefined  _ _ _ _ _ xtors) = S.unions (freeTVars <$> xtors)
  freeTVars (TyI64 _ _)                        = S.empty
  freeTVars (TyF64 _ _)                        = S.empty
  freeTVars (TyChar _ _)                       = S.empty
  freeTVars (TyString _ _)                     = S.empty
  freeTVars (TyFlipPol _ ty)                   = freeTVars ty

instance FreeTVars (PrdCnsType pol) where
  freeTVars (PrdCnsType _ ty) = freeTVars ty

instance FreeTVars (VariantType pol) where
  freeTVars (CovariantType ty)     = freeTVars ty
  freeTVars (ContravariantType ty) = freeTVars ty

instance FreeTVars (LinearContext pol) where
  freeTVars ctxt = S.unions (freeTVars <$> ctxt)

instance FreeTVars (XtorSig pol) where
  freeTVars sig = freeTVars sig.sig_args

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
  BisubstMap UniVT    = (Map UniTVar (Typ Pos, Typ Neg), Map KVar AnyKind)
  BisubstMap SkolemVT = Map SkolemTVar (Typ Pos, Typ Neg)
  BisubstMap RecVT    = Map RecTVar (Typ Pos, Typ Neg)

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
    case M.lookup tv (fst bisubst.bisubst_map) of
      Nothing -> zonkKind (snd bisubst.bisubst_map) ty
      Just (tyPos,_) -> zonkKind (snd bisubst.bisubst_map) tyPos
  zonk UniRep bisubst ty@(TyUniVar _ NegRep _ tv) = 
    case M.lookup tv (fst bisubst.bisubst_map) of
      Nothing -> zonkKind (snd bisubst.bisubst_map) ty 
      Just (_,tyNeg) -> zonkKind (snd bisubst.bisubst_map) tyNeg 
  zonk SkolemRep _ ty@TyUniVar{} = ty
  zonk RecRep _ ty@TyUniVar{} = ty
  zonk UniRep bisubst ty@TySkolemVar{} = zonkKind (snd bisubst.bisubst_map) ty
  zonk SkolemRep bisubst ty@(TySkolemVar _ PosRep _ tv) = case M.lookup tv bisubst.bisubst_map of
     Nothing -> ty -- Recursive variable!
     Just (tyPos,_) -> tyPos
  zonk SkolemRep bisubst ty@(TySkolemVar _ NegRep _ tv) = case M.lookup tv bisubst.bisubst_map of
     Nothing -> ty -- Recursive variable!
     Just (_,tyNeg) -> tyNeg
  zonk RecRep _ ty@TySkolemVar{} = ty
  zonk UniRep bisubst ty@TyRecVar{} = zonkKind (snd bisubst.bisubst_map) ty
  zonk SkolemRep _ ty@TyRecVar{} = ty
  zonk RecRep bisubst ty@(TyRecVar _ PosRep _ tv) = case M.lookup tv bisubst.bisubst_map of
    Nothing -> ty
    Just (tyPos,_) -> tyPos
  zonk RecRep bisubst ty@(TyRecVar _ NegRep _ tv) = case M.lookup tv bisubst.bisubst_map of
    Nothing -> ty
    Just (_,tyNeg) -> tyNeg
  zonk UniRep bisubst (TyData loc rep mk xtors) =
     let knd = zonkKind (snd bisubst.bisubst_map) mk in
     TyData loc rep knd (zonk UniRep bisubst <$> xtors)
  zonk vt bisubst (TyData loc rep mk xtors) =
     TyData loc rep  mk (zonk vt bisubst <$> xtors)
  zonk UniRep bisubst (TyCodata loc rep mk xtors) =
     let knd = zonkKind (snd bisubst.bisubst_map) mk in
     TyCodata loc rep knd (zonk UniRep bisubst <$> xtors)
  zonk vt bisubst (TyCodata loc rep mk xtors) =
     TyCodata loc rep mk (zonk vt bisubst <$> xtors)
  zonk UniRep bisubst (TyDataRefined loc rep pk tn rv xtors) =
     let knd = zonkKind (snd bisubst.bisubst_map)  pk in
     TyDataRefined loc rep knd tn rv (zonk UniRep bisubst <$> xtors)
  zonk vt bisubst (TyDataRefined loc rep pk tn rv xtors) =
     TyDataRefined loc rep pk tn rv (zonk vt bisubst <$> xtors)
  zonk UniRep bisubst (TyCodataRefined loc rep pk tn rv xtors) =
     let knd = zonkKind (snd bisubst.bisubst_map) pk in
     TyCodataRefined loc rep knd tn rv (zonk UniRep bisubst <$> xtors)
  zonk vt bisubst (TyCodataRefined loc rep pk tn rv xtors) =
     TyCodataRefined loc rep pk tn rv (zonk vt bisubst <$> xtors)
  zonk UniRep bisubst (TyNominal loc rep pk tn) = 
    let knd = zonkKind (snd $ bisubst.bisubst_map) pk in
    TyNominal loc rep knd tn 
  zonk _ _ (TyNominal loc rep kind tn) =
     TyNominal loc rep kind tn 
  zonk vt bisubst (TyApp loc rep ty args) = 
    TyApp loc rep (zonk vt bisubst ty) (zonk vt bisubst <$> args)
  zonk vt bisubst (TySyn loc rep nm ty) =
     TySyn loc rep nm (zonk vt bisubst ty)
  zonk UniRep bisubst (TyTop loc pk) = 
    let knd = zonkKind (snd $ bisubst.bisubst_map) pk in
    TyTop loc knd
  zonk _vt _ (TyTop loc mk) =
    TyTop loc mk
  zonk UniRep bisubst (TyBot loc pk) = 
    let knd = zonkKind (snd $ bisubst.bisubst_map) pk in
    TyBot loc knd
  zonk _vt _ (TyBot loc pk) =
    TyBot loc pk
  zonk UniRep bisubst (TyUnion loc pk ty1 ty2) = 
    let knd = zonkKind (snd $ bisubst.bisubst_map) pk in
    TyUnion loc knd (zonk UniRep bisubst ty1) (zonk UniRep bisubst ty2)
  zonk vt bisubst (TyUnion loc pknd ty ty') =
    TyUnion loc pknd (zonk vt bisubst ty) (zonk vt bisubst ty')
  zonk UniRep bisubst (TyInter loc pk ty1 ty2) = 
    let knd = zonkKind (snd bisubst.bisubst_map) pk in
    TyInter loc knd (zonk UniRep bisubst ty1) (zonk UniRep bisubst ty2)
  zonk vt bisubst (TyInter loc pknd ty ty') =
    TyInter loc pknd (zonk vt bisubst ty) (zonk vt bisubst ty')
  zonk RecRep bisubst (TyRec loc rep tv ty) =
    let bisubst' = MkBisubstitution $ M.delete tv bisubst.bisubst_map
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
    TypeScheme {ts_loc = loc, ts_vars = zonkKind (snd bisubst.bisubst_map) <$> tvars, ts_monotype = zonk UniRep bisubst ty}
  zonk _ _ _ = error "Not implemented"

class ZonkKind (a::Type) where 
  zonkKind :: Map KVar AnyKind -> a -> a

instance ZonkKind PolyKind where 
  zonkKind bisubst kindV@(KindVar kv) = case M.lookup kv bisubst of
    Nothing -> kindV
    Just (MkPknd pk) -> pk
    Just _ -> error "should never happen"
  zonkKind _ pk = pk

instance ZonkKind MonoKind where 
  zonkKind _ mk = mk

instance ZonkKind EvaluationOrder where 
  zonkKind _ eo = eo

instance ZonkKind AnyKind where 
  zonkKind bisubst (MkPknd pk) = MkPknd $ zonkKind bisubst pk
  zonkKind _ primk = primk

instance ZonkKind (Typ pol) where 
  zonkKind bisubst (TySkolemVar loc rep pk tv) = 
    TySkolemVar loc rep (zonkKind bisubst pk) tv 
  zonkKind bisubst (TyUniVar loc rep pk tv) = 
    TyUniVar loc rep (zonkKind bisubst pk) tv 
  zonkKind bisubst (TyRecVar loc rep pk tv) = 
    TyRecVar loc rep (zonkKind bisubst pk) tv
  zonkKind bisubst (TyData loc pol mk xtors) = 
    TyData loc pol (zonkKind bisubst mk) (zonkKind bisubst <$> xtors)
  zonkKind bisubst (TyCodata loc pol mk xtors) = 
    TyCodata loc pol (zonkKind bisubst mk) (zonkKind bisubst <$> xtors)
  zonkKind bisubst (TyDataRefined loc pol pk tyn rv xtors) = 
    TyDataRefined loc pol (zonkKind bisubst pk) tyn rv (zonkKind bisubst <$> xtors)
  zonkKind bisubst (TyCodataRefined loc pol pk tyn rv xtors) = 
    TyCodataRefined loc pol (zonkKind bisubst pk) tyn rv (zonkKind bisubst <$> xtors)
  zonkKind bisubst (TyNominal loc pol pk tyn) = 
    TyNominal loc pol (zonkKind bisubst pk) tyn 
  zonkKind bisubst (TyApp loc pol ty args) = 
    TyApp loc pol (zonkKind bisubst ty) (zonkKind bisubst <$> args)
  zonkKind bisubst (TySyn loc pol tyn ty) = 
    TySyn loc pol tyn (zonkKind bisubst ty)
  zonkKind bisubst (TyTop loc pk) = 
    TyTop loc (zonkKind bisubst pk)
  zonkKind bisubst (TyBot loc pk) = 
    TyBot loc (zonkKind bisubst pk)
  zonkKind bisubst (TyUnion loc pk ty1 ty2) = 
    TyUnion loc (zonkKind bisubst pk) (zonkKind bisubst ty1) (zonkKind bisubst ty2)
  zonkKind bisubst (TyInter loc pk ty1 ty2) = 
    TyInter loc (zonkKind bisubst pk) (zonkKind bisubst ty1) (zonkKind bisubst ty2)
  zonkKind bisubst (TyRec loc pol rv ty) = 
    TyRec loc pol rv (zonkKind bisubst ty)
  zonkKind _ ty@TyI64{} = ty
  zonkKind _ ty@TyF64{} = ty
  zonkKind _ ty@TyChar{} = ty
  zonkKind _ ty@TyString{} = ty
  zonkKind bisubst (TyFlipPol pol ty) = TyFlipPol pol (zonkKind bisubst ty)


instance ZonkKind (XtorSig pol) where 
  zonkKind bisubst (MkXtorSig { sig_name = nm, sig_args = args }) = 
    MkXtorSig {sig_name = nm, sig_args = zonkKind bisubst <$> args}
 
instance ZonkKind (LinearContext pol) where 
  zonkKind bisubst = map (zonkKind bisubst)

instance ZonkKind (PrdCnsType pol) where 
  zonkKind bisubst (PrdCnsType rep ty) = PrdCnsType rep (zonkKind bisubst ty)


instance ZonkKind (VariantType pol) where 
  zonkKind bisubst (CovariantType ty) = CovariantType (zonkKind bisubst ty)
  zonkKind bisubst (ContravariantType ty) = ContravariantType (zonkKind bisubst ty)

instance ZonkKind KindedSkolem where 
  zonkKind bisubst (sk,mk) = (sk, zonkKind bisubst mk)

-- This is probably not 100% correct w.r.t alpha-renaming. Postponed until we have a better repr. of types.
unfoldRecType :: Typ pol -> Typ pol
unfoldRecType recty@(TyRec _ PosRep var ty) = zonk RecRep (MkBisubstitution (M.fromList [(var,(recty, error "unfoldRecType"))])) ty
unfoldRecType recty@(TyRec _ NegRep var ty) = zonk RecRep (MkBisubstitution (M.fromList [(var,(error "unfoldRecType", recty))])) ty
unfoldRecType ty = ty
