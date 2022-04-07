module Syntax.RST.Types where

import Data.List (nub)
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
  TyVar :: PolarityRep pol -> Maybe MonoKind -> TVar -> Typ pol
  -- | We have to duplicate TyStructData and TyStructCodata here due to restrictions of the deriving mechanism of Haskell.
  -- | Refinement types are represented by the presence of the TypeName parameter
  TyData   :: PolarityRep pol -> Maybe TypeName -> [XtorSig pol]   -> Typ pol
  TyCodata :: PolarityRep pol -> Maybe TypeName -> [XtorSig (FlipPol pol)] -> Typ pol
  -- | Nominal types with arguments to type parameters (contravariant, covariant)
  TyNominal :: PolarityRep pol -> Maybe MonoKind -> TypeName -> [VariantType pol] -> Typ pol
  -- | PosRep = Union, NegRep = Intersection
  TySet :: PolarityRep pol -> Maybe MonoKind -> [Typ pol] -> Typ pol
  TyRec :: PolarityRep pol -> TVar -> Typ pol -> Typ pol
  TyPrim :: PolarityRep pol -> PrimitiveType -> Typ pol

deriving instance Eq (Typ Pos)
deriving instance Eq (Typ Neg)
deriving instance Ord (Typ Pos)
deriving instance Ord (Typ Neg)
deriving instance Show (Typ Pos)
deriving instance Show (Typ Neg)

getPolarity :: Typ pol -> PolarityRep pol
getPolarity (TyVar rep _ _)         = rep
getPolarity (TyData rep _ _)        = rep
getPolarity (TyCodata rep _ _)      = rep
getPolarity (TyNominal rep _ _ _)   = rep
getPolarity (TySet rep _ _)         = rep
getPolarity (TyRec rep _ _)         = rep
getPolarity (TyPrim rep _)          = rep

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

freeTypeVars :: Typ pol -> [TVar]
freeTypeVars = nub . freeTypeVars'
  where
    freeTypeVars' :: Typ pol -> [TVar]
    freeTypeVars' (TyVar _ _ tv) = [tv]
    freeTypeVars' (TySet _ _ ts) = concatMap freeTypeVars' ts
    freeTypeVars' (TyRec _ v t)  = filter (/= v) (freeTypeVars' t)
    freeTypeVars' (TyNominal _ _ _ args) = concatMap freeTypeVarsVarCov args
    freeTypeVars' (TyData _ _ xtors) = concatMap freeTypeVarsXtorSig xtors
    freeTypeVars' (TyCodata _ _ xtors) = concatMap freeTypeVarsXtorSig xtors
    freeTypeVars' (TyPrim _ _) = []

    freeTypeVarsPC :: PrdCnsType pol -> [TVar]
    freeTypeVarsPC (PrdCnsType _ ty) = freeTypeVars' ty

    freeTypeVarsVarCov :: VariantType pol -> [TVar]
    freeTypeVarsVarCov (CovariantType ty)       = freeTypeVars' ty
    freeTypeVarsVarCov (ContravariantType ty) = freeTypeVars' ty

    freeTypeVarsCtxt :: LinearContext pol -> [TVar]
    freeTypeVarsCtxt ctxt = concat (freeTypeVarsPC <$> ctxt)

    freeTypeVarsXtorSig :: XtorSig pol -> [TVar]
    freeTypeVarsXtorSig (MkXtorSig _ ctxt) = freeTypeVarsCtxt ctxt


-- | Generalize over all free type variables of a type.
generalize :: Typ pol -> TypeScheme pol
generalize ty = TypeScheme defaultLoc (freeTypeVars ty) ty

------------------------------------------------------------------------------
-- Bisubstitution and Zonking
------------------------------------------------------------------------------

data Bisubstitution = MkBisubstitution { uvarSubst :: Map TVar (Typ Pos, Typ Neg) }

-- | Class of types for which a Bisubstitution can be applied.
class Zonk (a :: Type) where
  zonk :: Bisubstitution -> a -> a

instance Zonk (Typ pol) where
  zonk bisubst ty@(TyVar PosRep _ tv) = case M.lookup tv (uvarSubst bisubst) of
     Nothing -> ty -- Recursive variable!
     Just (tyPos,_) -> tyPos
  zonk bisubst ty@(TyVar NegRep _ tv) = case M.lookup tv (uvarSubst bisubst) of
     Nothing -> ty -- Recursive variable!
     Just (_,tyNeg) -> tyNeg
  zonk bisubst (TyData rep tn xtors) =
     TyData rep tn (zonk bisubst <$> xtors)
  zonk bisubst (TyCodata rep tn xtors) =
     TyCodata rep tn (zonk bisubst <$> xtors)
  zonk bisubst (TyNominal rep kind tn args) =
     TyNominal rep kind tn (zonk bisubst <$> args)
  zonk bisubst (TySet rep kind tys) =
     TySet rep kind (zonk bisubst <$> tys)
  zonk bisubst (TyRec rep tv ty) =
     TyRec rep tv (zonk bisubst ty)
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
unfoldRecType recty@(TyRec PosRep var ty) = zonk (MkBisubstitution (M.fromList [(var,(recty, error "unfoldRecType"))])) ty
unfoldRecType recty@(TyRec NegRep var ty) = zonk (MkBisubstitution (M.fromList [(var,(error "unfoldRecType", recty))])) ty
unfoldRecType ty = ty

------------------------------------------------------------------------------
-- Data Type declarations
------------------------------------------------------------------------------

data DataDecl = NominalDecl
  { data_refined :: IsRefined
  , data_name :: TypeName
  , data_polarity :: DataCodata
  , data_kind :: PolyKind
  , data_xtors :: ([XtorSig Pos], [XtorSig Neg])
  } deriving (Show)
