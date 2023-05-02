module Syntax.TST.Types where
import Data.Set (Set)
import Data.Set qualified as S
import Data.Map (Map)
import Data.Map qualified as M
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE (toList) 
import Data.Maybe (fromMaybe)
import Data.Kind ( Type )
import Syntax.RST.Types (Polarity(..), PolarityRep(..), FlipPol ,PrdCnsFlip)
import Syntax.CST.Types ( PrdCnsRep(..), PrdCns(..), Arity, Variance(..), EvaluationOrder(..), PolyKind(..), MonoKind(..))
import Syntax.CST.Names ( MethodName, SkolemTVar, KVar(..), XtorName )
import Syntax.RST.Names
import Syntax.RST.Kinds
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
  TySkolemVar     :: Loc -> PolarityRep pol -> AnyKind -> SkolemTVar -> Typ pol
  TyUniVar        :: Loc -> PolarityRep pol -> AnyKind -> UniTVar -> Typ pol
  TyRecVar        :: Loc -> PolarityRep pol -> PolyKind -> RecTVar -> Typ pol
  -- | We have to duplicate TyStructData and TyStructCodata here due to restrictions of the deriving mechanism of Haskell.
  -- | Refinement types are represented by the presence of the TypeName parameter
  TyData          :: Loc -> PolarityRep pol -> EvaluationOrder           -> [XtorSig pol]           -> Typ pol
  TyCodata        :: Loc -> PolarityRep pol -> EvaluationOrder           -> [XtorSig (FlipPol pol)] -> Typ pol
  TyDataRefined   :: Loc -> PolarityRep pol -> PolyKind   -> [SkolemTVar] -> RnTypeName  -> [XtorSig pol]           -> Typ pol
  TyCodataRefined :: Loc -> PolarityRep pol -> PolyKind   -> [SkolemTVar] -> RnTypeName  -> [XtorSig (FlipPol pol)] -> Typ pol
  -- | Nominal types with arguments to type parameters (contravariant, covariant)
  TyNominal       :: Loc -> PolarityRep pol -> PolyKind -> RnTypeName -> Typ pol
  TyApp           :: Loc -> PolarityRep pol -> EvaluationOrder -> Typ pol    -> RnTypeName -> NonEmpty (VariantType pol) -> Typ pol
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
  getLoc (TyDataRefined loc _  _ _ _ _ ) = loc
  getLoc (TyCodataRefined loc _ _ _ _ _) = loc
  getLoc (TyNominal loc _ _ _)           = loc
  getLoc (TyApp loc _ _ _ _ _)           = loc
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
getPolarity (TyDataRefined _ rep  _  _ _ _)  = rep
getPolarity (TyCodataRefined _ rep  _ _ _ _) = rep
getPolarity (TyNominal _ rep _ _)            = rep
getPolarity (TyApp _ rep _ _ _ _)            = rep
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
  getKind (TySkolemVar _ _ knd _)          = knd
  getKind (TyUniVar _ _ knd _)            = knd
  getKind (TyRecVar _ _ pk _)             = MkPknd pk 
  getKind (TyData _ _ eo _ )              = MkPknd (MkPolyKind [] eo)
  getKind (TyCodata _ _ eo _ )            = MkPknd (MkPolyKind [] eo)
  getKind (TyDataRefined _ _ pk _ _ _)      = MkPknd pk
  getKind (TyCodataRefined _ _ pk _  _ _)    = MkPknd pk
  getKind (TyNominal _ _ pk _ )           = MkPknd pk
  getKind (TyApp _ _ eo _ _ _)            = MkPknd (MkPolyKind [] eo)
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
  freeTVars :: a -> Set (SkolemTVar, AnyKind)

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
  freeTVars (TyApp _ _ _ ty _ args)            = S.union (freeTVars ty) (S.unions (freeTVars <$> args))
  freeTVars (TySyn _ _ _ ty)                   = freeTVars ty
  freeTVars (TyData _  _ _ xtors)              = S.unions (freeTVars <$> xtors)
  freeTVars (TyCodata _ _ _ xtors)             = S.unions (freeTVars <$> xtors)
  freeTVars (TyDataRefined _ _ _ argVars _ xtors)    = do 
    let freeVars = S.unions (freeTVars <$> xtors)
    let f (sk,_) = sk `notElem` argVars
    S.filter f freeVars 
  freeTVars (TyCodataRefined  _ _ _ argVars _ xtors) = do
    let freeVars = S.unions (freeTVars <$> xtors)
    let f (sk,_) = sk `notElem` argVars
    S.filter f freeVars 
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
generalize ty = do 
  let freeVars = S.toList $ freeTVars ty
  TypeScheme defaultLoc (filterVars freeVars)  ty
  where 
    filterVars :: [(SkolemTVar, AnyKind)] -> [(SkolemTVar, PolyKind)]
    filterVars [] = []
    filterVars ((sk,MkPknd pk):rst) = (sk,pk) : filterVars rst
    filterVars ((_,_):rst) = filterVars rst


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
  zonk UniRep bisubst (TyDataRefined loc rep pk argVars tn xtors) =
     let knd = zonkKind (snd bisubst.bisubst_map)  pk in
     TyDataRefined loc rep knd argVars tn (zonk UniRep bisubst <$> xtors)
  zonk SkolemRep bisubst (TyDataRefined loc rep pk argVars tn xtors) = do
     let bisubstNew = MkBisubstitution $ foldr M.delete bisubst.bisubst_map argVars
     TyDataRefined loc rep pk argVars tn (zonk SkolemRep bisubstNew <$> xtors)
  zonk vt bisubst (TyDataRefined loc rep pk argVars tn xtors) =
     TyDataRefined loc rep pk argVars tn (zonk vt bisubst <$> xtors)
  zonk UniRep bisubst (TyCodataRefined loc rep pk argVars tn xtors) =
     let knd = zonkKind (snd bisubst.bisubst_map) pk in
     TyCodataRefined loc rep knd argVars tn (zonk UniRep bisubst <$> xtors)
  zonk SkolemRep bisubst (TyCodataRefined loc rep pk argVars tn xtors) = do
     let bisubstNew = MkBisubstitution $ foldr M.delete bisubst.bisubst_map argVars 
     TyCodataRefined loc rep pk argVars tn (zonk SkolemRep bisubstNew <$> xtors) 
  zonk vt bisubst (TyCodataRefined loc rep pk argVars tn xtors) =
     TyCodataRefined loc rep pk argVars tn (zonk vt bisubst <$> xtors)
  zonk UniRep bisubst (TyNominal loc rep pk tn) = 
    let knd = zonkKind (snd $ bisubst.bisubst_map) pk in
    TyNominal loc rep knd tn 
  zonk _ _ (TyNominal loc rep kind tn) =
     TyNominal loc rep kind tn 
  zonk vt bisubst (TyApp loc rep eo ty tyn args) = 
    TyApp loc rep eo (zonk vt bisubst ty) tyn (zonk vt bisubst <$> args)
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
  zonkKind bisubst knd@(MkPknd (KindVar kv)) = Data.Maybe.fromMaybe knd (M.lookup kv bisubst)
  zonkKind _ knd = knd

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
  zonkKind bisubst (TyDataRefined loc pol pk argVars tyn xtors) = 
    TyDataRefined loc pol (zonkKind bisubst pk) argVars tyn (zonkKind bisubst <$> xtors)
  zonkKind bisubst (TyCodataRefined loc pol pk argVars tyn xtors) = 
    TyCodataRefined loc pol (zonkKind bisubst pk) argVars tyn (zonkKind bisubst <$> xtors)
  zonkKind bisubst (TyNominal loc pol pk tyn) = 
    TyNominal loc pol (zonkKind bisubst pk) tyn 
  zonkKind bisubst (TyApp loc pol eo ty tyn args) = 
    TyApp loc pol eo (zonkKind bisubst ty) tyn (zonkKind bisubst <$> args)
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

-----
-- replace type with other skolem (used for arguments of refinement types)
-- replaces the given type at given polarity in a with the skolem variable
----
class ReplType (a::Type) where 
  replType :: PolarityRep pol -> SkolemTVar -> Typ pol -> a -> a

instance ReplType (Typ pol) where 
  replType PosRep sk'' (TySkolemVar _ _ _ sk') ty@(TySkolemVar loc PosRep knd sk) = 
    if sk==sk' then TySkolemVar loc PosRep knd sk'' else ty
  replType NegRep sk'' (TySkolemVar _ _ _ sk') ty@(TySkolemVar loc NegRep knd sk) = 
    if sk==sk' then TySkolemVar loc NegRep knd sk'' else ty
  replType _ _ _ ty@TySkolemVar{} = ty

  replType PosRep sk (TyUniVar _ _ _ uv') ty@(TyUniVar loc PosRep knd uv) = 
    if uv == uv' then TySkolemVar loc PosRep knd sk else ty
  replType NegRep sk (TyUniVar _ _ _ uv') ty@(TyUniVar loc NegRep knd uv) = 
    if uv == uv' then TySkolemVar loc NegRep knd sk else ty
  replType _ _ _ ty@TyUniVar{} = ty

  replType PosRep sk (TyRecVar _ _ _ rv') ty@(TyRecVar loc PosRep pk rv) = 
    if rv == rv' then TySkolemVar loc PosRep (MkPknd pk) sk else ty
  replType NegRep sk (TyRecVar _ _ _ rv') ty@(TyRecVar loc NegRep pk rv) = 
    if rv == rv' then TySkolemVar loc NegRep (MkPknd pk) sk else ty
  replType _ _ _ ty@TyRecVar{} = ty

  replType PosRep sk ty@(TyData _ _ _ xtors') (TyData loc PosRep eo xtors) = 
    if xtors == xtors' then TySkolemVar loc PosRep (MkPknd (MkPolyKind [] eo)) sk
    else TyData loc PosRep eo (replType PosRep sk ty <$> xtors)
  replType NegRep sk ty@(TyData _ _ _ xtors') (TyData loc NegRep eo xtors) = 
    if xtors == xtors' then TySkolemVar loc NegRep (MkPknd (MkPolyKind [] eo)) sk
    else TyData loc NegRep eo (replType NegRep sk ty <$> xtors)
  replType rep sk ty (TyData loc pol eo xtors) = TyData loc pol eo (replType rep sk ty <$> xtors)

  replType PosRep sk ty@(TyCodata _ _ _ xtors') (TyCodata loc PosRep eo xtors) = 
    if xtors == xtors' then TySkolemVar loc PosRep (MkPknd (MkPolyKind [] eo)) sk
    else TyCodata loc PosRep eo (replType PosRep sk ty <$> xtors)
  replType NegRep sk ty@(TyCodata _ _ _ xtors') (TyCodata loc NegRep eo xtors) = 
    if xtors == xtors' then TySkolemVar loc NegRep (MkPknd (MkPolyKind [] eo)) sk
    else TyCodata loc NegRep eo (replType NegRep sk ty <$> xtors)
  replType rep sk ty (TyCodata loc pol eo xtors) = TyCodata loc pol eo (replType rep sk ty <$> xtors)

  replType PosRep sk ty@(TyDataRefined _ _ _ _ tyn' xtors') (TyDataRefined loc PosRep pk argVars tyn xtors) = 
    if tyn == tyn' && xtors == xtors' then 
      TySkolemVar loc PosRep (MkPknd pk) sk 
    else TyDataRefined loc PosRep pk argVars tyn (replType PosRep sk ty <$> xtors)
  replType NegRep sk ty@(TyDataRefined _ _ _ _ tyn' xtors') (TyDataRefined loc NegRep pk argVars tyn xtors) = 
    if tyn == tyn' && xtors == xtors' then 
      TySkolemVar loc NegRep (MkPknd pk) sk 
    else TyDataRefined loc NegRep pk argVars tyn (replType NegRep sk ty <$> xtors)
  replType rep sk ty (TyDataRefined loc pol pk argVars tyn xtors) = 
    TyDataRefined loc pol pk argVars tyn (replType rep sk ty <$> xtors)

  replType PosRep sk ty@(TyCodataRefined _ _ _ _ tyn' xtors') (TyCodataRefined loc PosRep pk argVars tyn xtors) = 
    if tyn == tyn' && xtors == xtors' then 
      TySkolemVar loc PosRep (MkPknd pk) sk 
    else TyCodataRefined loc PosRep pk argVars tyn (replType PosRep sk ty <$> xtors)
  replType NegRep sk ty@(TyCodataRefined _ _ _ _ tyn' xtors') (TyCodataRefined loc NegRep pk argVars tyn xtors) = 
    if tyn == tyn' && xtors == xtors' then 
      TySkolemVar loc NegRep (MkPknd pk) sk 
    else TyCodataRefined loc NegRep pk argVars tyn (replType NegRep sk ty <$> xtors)
  replType rep sk ty (TyCodataRefined loc pol pk argVars tyn xtors) = 
    TyCodataRefined loc pol pk argVars tyn (replType rep sk ty <$> xtors)

  replType PosRep sk (TyNominal _ _ _ tyn') ty@(TyNominal loc PosRep pk tyn) = 
    if tyn == tyn' then 
      TySkolemVar loc PosRep (MkPknd pk) sk
    else ty
  replType NegRep sk (TyNominal _ _ _ tyn') ty@(TyNominal loc NegRep pk tyn) = 
    if tyn == tyn' then 
      TySkolemVar loc NegRep (MkPknd pk) sk
    else ty

  replType _ _ _ ty@TyNominal{} = ty

  replType PosRep sk ty@(TyApp _ _ _ ty1' tyn' args') (TyApp loc PosRep eo ty1 tyn args) = 
    if tyn' == tyn && ty1 == ty1' && args' == args then
      TySkolemVar loc PosRep (MkPknd $ MkPolyKind [] eo) sk
    else 
      TyApp loc PosRep eo (replType PosRep sk ty ty1) tyn (replType PosRep sk ty <$> args)
  replType NegRep sk ty@(TyApp _ _ _ ty1' tyn' args') (TyApp loc NegRep eo ty1 tyn args) = 
    if tyn' == tyn && ty1 == ty1' && args' == args then
      TySkolemVar loc NegRep (MkPknd $ MkPolyKind [] eo) sk
    else 
      TyApp loc NegRep eo (replType NegRep sk ty ty1) tyn (replType NegRep sk ty <$> args)
  replType rep ty sk (TyApp loc pol eo ty1 tyn args) = 
    TyApp loc pol eo (replType rep ty sk ty1) tyn (replType rep ty sk <$> args)

  replType PosRep sk ty@(TySyn _ _ tyn' ty1') (TySyn loc PosRep tyn ty1) = 
    if tyn' == tyn && ty1' == ty1 then
      TySkolemVar loc PosRep (getKind ty1) sk
    else TySyn loc PosRep tyn (replType PosRep sk ty ty1)
  replType NegRep sk ty@(TySyn _ _ tyn' ty1') (TySyn loc NegRep tyn ty1) = 
    if tyn' == tyn && ty1' == ty1 then
      TySkolemVar loc NegRep (getKind ty1) sk
    else TySyn loc NegRep tyn (replType NegRep sk ty ty1)
  replType rep sk ty (TySyn loc pol tyn ty1) = TySyn loc pol tyn (replType rep sk ty ty1)
 
  replType PosRep sk TyBot{} (TyBot loc knd) = TySkolemVar loc PosRep knd sk
  replType _ _ _ ty@TyBot{} = ty 

  replType NegRep sk TyTop{} (TyTop loc knd) = TySkolemVar loc NegRep knd sk
  replType _ _ _ ty@TyTop{} = ty 

  replType PosRep sk ty@(TyUnion _ _ ty1' ty2') (TyUnion loc knd ty1 ty2) = 
    if ty1' == ty1 && ty2' == ty2 then 
      TySkolemVar loc PosRep knd sk
    else TyUnion loc knd (replType PosRep sk ty ty1) (replType PosRep sk ty ty2) 
  replType rep sk ty (TyUnion loc knd ty1 ty2) = TyUnion loc knd (replType rep sk ty ty1) (replType rep sk ty ty2)

  replType NegRep sk ty@(TyInter _ _ ty1' ty2') (TyInter loc knd ty1 ty2) = 
    if ty1' == ty1 && ty2' == ty2 then 
      TySkolemVar loc NegRep knd sk
    else TyInter loc knd (replType NegRep sk ty ty1) (replType NegRep sk ty ty2) 
  replType rep sk ty (TyInter loc knd ty1 ty2) = TyInter loc knd (replType rep sk ty ty1) (replType rep sk ty ty2)

  replType PosRep sk ty'@(TyRec _ _ rv' ty1') (TyRec loc PosRep rv ty1) = 
    if rv'==rv && ty1' == ty1 then 
      TySkolemVar loc PosRep (getKind ty1) sk
    else 
      TyRec loc PosRep rv (replType PosRep sk ty' ty1)
  replType NegRep sk ty'@(TyRec _ _ rv' ty1') (TyRec loc NegRep rv ty1) = 
    if rv'==rv && ty1' == ty1 then 
      TySkolemVar loc NegRep (getKind ty1) sk
    else 
      TyRec loc NegRep rv (replType NegRep sk ty' ty1)
  replType rep sk ty (TyRec loc pol rv ty1) = TyRec loc pol rv (replType rep sk ty ty1)
   
  replType PosRep sk TyI64{} (TyI64 loc PosRep) = TySkolemVar loc PosRep MkI64 sk
  replType NegRep sk TyI64{} (TyI64 loc NegRep) = TySkolemVar loc NegRep MkI64 sk
  replType _ _ _ ty@TyI64{} = ty 

  replType PosRep sk TyF64{} (TyF64 loc PosRep) = TySkolemVar loc PosRep MkF64 sk
  replType NegRep sk TyF64{} (TyF64 loc NegRep) = TySkolemVar loc NegRep MkF64 sk
  replType _ _ _ ty@TyF64{} = ty 

  replType PosRep sk TyChar{} (TyChar loc PosRep) = TySkolemVar loc PosRep MkChar sk
  replType NegRep sk TyChar{} (TyChar loc NegRep) = TySkolemVar loc NegRep MkChar sk
  replType _ _ _ ty@TyChar{} = ty 

  replType PosRep sk TyString{} (TyString loc PosRep) = TySkolemVar loc PosRep MkString sk
  replType NegRep sk TyString{} (TyString loc NegRep) = TySkolemVar loc NegRep MkString sk
  replType _ _ _ ty@TyString{} = ty 

  replType PosRep sk ty@(TyFlipPol _ ty1') (TyFlipPol PosRep ty1) = 
    if ty1' == ty1 then TySkolemVar (getLoc ty1) PosRep (getKind ty1) sk
    else TyFlipPol PosRep (replType PosRep sk ty ty1)

  replType NegRep sk ty@(TyFlipPol _ ty1') (TyFlipPol NegRep ty1) = 
    if ty1' == ty1 then TySkolemVar (getLoc ty1) NegRep (getKind ty1) sk
    else TyFlipPol NegRep (replType NegRep sk ty ty1)
  
  replType rep sk ty (TyFlipPol pol ty1) = TyFlipPol pol (replType rep sk ty ty1)


instance ReplType (XtorSig pol) where 
  replType rep ty sk (MkXtorSig nm args) = MkXtorSig nm (replType rep ty sk <$> args) 

instance ReplType (PrdCnsType pol) where 
  replType rep ty sk (PrdCnsType pol ty') = PrdCnsType pol (replType rep ty sk ty')

instance ReplType (VariantType pol) where 
  replType rep ty sk (CovariantType ty') = CovariantType (replType rep ty sk ty')
  replType rep ty sk (ContravariantType ty') = ContravariantType (replType rep ty sk ty')

-- this class is used for refinement xtors 
-- the first argument is the type in the declaration and the second is the inferred type 
-- we have to replace the types inside the inferred xtor with skolem variables for type arguments 
-- to do this we check where the skolems are in the declaration and return the corresponding inferred type
class GetDeclReplacements (a::Type) (b::Type) where 
  getDeclReplacements :: a -> b -> ([(Typ Pos, SkolemTVar)], [(Typ Neg,SkolemTVar)])

instance GetDeclReplacements (Typ pol1) (Typ pol2) where 
 getDeclReplacements (TySkolemVar _ _ _ sk) ty =  case getPolarity ty of PosRep -> ([(ty,sk)],[]); NegRep -> ([],[(ty,sk)])
 getDeclReplacements (TyData _ _ _ xtors) (TyData _ _ _ xtors') = do 
   let repls = uncurry getDeclReplacements <$> zip xtors' xtors
   (concatMap fst repls, concatMap snd repls)
 getDeclReplacements (TyCodata _ _ _ xtors) (TyCodata _ _ _ xtors')  = do 
   let repls = uncurry getDeclReplacements <$> zip  xtors' xtors
   (concatMap fst repls, concatMap snd repls)
 getDeclReplacements (TyDataRefined _ _ _ _ _ xtors) (TyDataRefined _ _ _ _ _ xtors') = do 
   let repls = uncurry getDeclReplacements <$> zip xtors' xtors
   (concatMap fst repls, concatMap snd repls)
 getDeclReplacements (TyCodataRefined _ _ _ _ _ xtors) (TyCodataRefined _ _ _ _ _ xtors') = do 
   let repls = uncurry getDeclReplacements <$> zip xtors' xtors
   (concatMap fst repls, concatMap snd repls)
 getDeclReplacements (TyApp _ _ _ ty _ args) (TyApp _ _ _ ty' _ args') = do 
   let (replPos,replNeg) = getDeclReplacements ty' ty 
   let repls = uncurry getDeclReplacements <$> zip (NE.toList args) (NE.toList args')
   (replPos ++ concatMap fst repls, replNeg ++ concatMap snd repls)
 getDeclReplacements (TySyn _ _ _ ty) (TySyn _ _ _ ty') = getDeclReplacements ty' ty
 getDeclReplacements (TyUnion _ _ ty1 ty2) (TyUnion _ _ ty1' ty2') = do 
   let (repl1Pos,repl1Neg) = getDeclReplacements ty1' ty1
   let (repl2Pos,repl2Neg) = getDeclReplacements ty2' ty2
   (repl1Pos ++ repl2Pos, repl1Neg++repl2Neg)
 getDeclReplacements (TyInter _ _ ty1 ty2) (TyInter _ _ ty1' ty2') = do 
   let (repl1Pos,repl1Neg) = getDeclReplacements ty1' ty1 
   let (repl2Pos,repl2Neg) = getDeclReplacements ty2' ty2
   (repl1Pos ++ repl2Pos, repl1Neg ++ repl2Neg) 
 getDeclReplacements (TyRec _ _ _  ty) (TyRec _ _ _ ty') = getDeclReplacements ty' ty
 getDeclReplacements (TyFlipPol _ ty) (TyFlipPol _ ty') =  getDeclReplacements ty' ty
 getDeclReplacements _ _ = ([],[])

instance GetDeclReplacements (XtorSig pol1) (XtorSig pol2) where 
  getDeclReplacements (MkXtorSig _ args1) (MkXtorSig _ args2) = getDeclReplacements args1 args2

instance GetDeclReplacements (LinearContext pol1) (LinearContext pol2) where 
  getDeclReplacements ctxt1 ctxt2 = do 
    let repls = uncurry getDeclReplacements <$> zip ctxt1 ctxt2
    (concatMap fst repls, concatMap snd repls)

instance GetDeclReplacements (PrdCnsType pol1) (PrdCnsType pol2) where 
  getDeclReplacements (PrdCnsType PrdRep ty) (PrdCnsType PrdRep ty') = getDeclReplacements ty ty'
  getDeclReplacements (PrdCnsType CnsRep ty) (PrdCnsType CnsRep ty') = getDeclReplacements ty ty'
  getDeclReplacements _ _ = error "impossible"

instance GetDeclReplacements (VariantType pol1) (VariantType pol2) where 
  getDeclReplacements (CovariantType ty) (CovariantType ty') = getDeclReplacements ty ty'
  getDeclReplacements (ContravariantType ty) (ContravariantType ty') = getDeclReplacements ty ty'
  getDeclReplacements _ _ = error "impossible"
