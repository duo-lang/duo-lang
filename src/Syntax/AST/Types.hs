module Syntax.AST.Types where

import Data.List (nub)
import Data.Map (Map)
import qualified Data.Map as M

import Syntax.Common
import Syntax.Primitives

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
  TyVar :: PolarityRep pol -> Maybe Kind -> TVar -> Typ pol
  -- | We have to duplicate TyStructData and TyStructCodata here due to restrictions of the deriving mechanism of Haskell.
  -- | Refinement types are represented by the presence of the TypeName parameter
  TyData   :: PolarityRep pol -> Maybe TypeName -> [XtorSig pol]   -> Typ pol
  TyCodata :: PolarityRep pol -> Maybe TypeName -> [XtorSig (FlipPol pol)] -> Typ pol
  -- | Nominal types with arguments to type parameters (contravariant, covariant)
  TyNominal :: PolarityRep pol -> Maybe Kind -> TypeName -> [Typ (FlipPol pol)] -> [Typ pol] -> Typ pol
  -- | PosRep = Union, NegRep = Intersection
  TySet :: PolarityRep pol -> Maybe Kind -> [Typ pol] -> Typ pol
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
getPolarity (TyNominal rep _ _ _ _) = rep
getPolarity (TySet rep _ _)         = rep
getPolarity (TyRec rep _ _)         = rep
getPolarity (TyPrim rep _)          = rep

------------------------------------------------------------------------------
-- Type Schemes
------------------------------------------------------------------------------

data TypeScheme (pol :: Polarity) = TypeScheme
  { ts_vars :: [TVar]
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
    freeTypeVars' (TyNominal _ _ _ conArgs covArgs) = concatMap freeTypeVars conArgs ++ concatMap freeTypeVars covArgs
    freeTypeVars' (TyData _ _ xtors) = concatMap freeTypeVarsXtorSig xtors
    freeTypeVars' (TyCodata _ _ xtors) = concatMap freeTypeVarsXtorSig xtors
    freeTypeVars' (TyPrim _ _) = []

    freeTypeVarsPC :: PrdCnsType pol -> [TVar]
    freeTypeVarsPC (PrdCnsType _ ty) = freeTypeVars' ty

    freeTypeVarsCtxt :: LinearContext pol -> [TVar]
    freeTypeVarsCtxt ctxt = concat (freeTypeVarsPC <$> ctxt)

    freeTypeVarsXtorSig :: XtorSig pol -> [TVar]
    freeTypeVarsXtorSig (MkXtorSig _ ctxt) = freeTypeVarsCtxt ctxt


-- | Generalize over all free type variables of a type.
generalize :: Typ pol -> TypeScheme pol
generalize ty = TypeScheme (freeTypeVars ty) ty

------------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------------

-- This is probably not 100% correct w.r.t alpha-renaming. Postponed until we have a better repr. of types.
unfoldRecType :: Typ pol -> Typ pol
unfoldRecType recty@(TyRec PosRep var ty) = substituteType (M.fromList [(var,(recty, error "unfoldRecType"))]) ty
unfoldRecType recty@(TyRec NegRep var ty) = substituteType (M.fromList [(var,(error "unfoldRecType",recty))]) ty
unfoldRecType ty = ty

substituteType :: Map TVar (Typ Pos, Typ Neg) -> Typ pol -> Typ pol
substituteType m var@(TyVar PosRep _ tv) =
  case M.lookup tv m of
    Nothing -> var
    Just (ty,_) -> ty
substituteType m var@(TyVar NegRep _ tv) =
  case M.lookup tv m of
    Nothing -> var
    Just (_,ty) -> ty
-- Other cases
substituteType m (TyData polrep mtn args) = TyData polrep mtn (substituteXtorSig m <$> args)
substituteType m (TyCodata polrep mtn args) = TyCodata polrep mtn (substituteXtorSig m <$> args)
substituteType m (TyNominal rep kind nm args_cov args_contra) = TyNominal rep kind nm (substituteType m <$> args_cov) (substituteType m <$> args_contra)
substituteType m (TySet rep kind args) = TySet rep kind (substituteType m <$> args)
substituteType m (TyRec rep tv arg) = TyRec rep tv (substituteType m arg)
substituteType _ t@(TyPrim _ _) = t

substituteXtorSig :: Map TVar (Typ Pos, Typ Neg) -> XtorSig pol -> XtorSig pol
substituteXtorSig m MkXtorSig { sig_name, sig_args } =  MkXtorSig sig_name (substituteContext m sig_args)

substituteContext :: Map TVar (Typ Pos, Typ Neg) -> LinearContext pol -> LinearContext pol
substituteContext m ctxt = substitutePCType m <$> ctxt

substitutePCType :: Map TVar (Typ Pos, Typ Neg) -> PrdCnsType pol -> PrdCnsType pol
substitutePCType m (PrdCnsType pc ty)= PrdCnsType pc $ substituteType m ty

------------------------------------------------------------------------------
-- Data Type declarations
------------------------------------------------------------------------------

data DataDecl = NominalDecl
  { data_refined :: IsRefined
  , data_name :: TypeName
  , data_polarity :: DataCodata
  , data_kind :: Kind
  , data_xtors :: ([XtorSig Pos], [XtorSig Neg])
  , data_params :: TParams
  } deriving (Show)
