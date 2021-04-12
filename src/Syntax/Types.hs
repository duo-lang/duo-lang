module Syntax.Types where

import Data.Map (Map)
import qualified Data.Map as M
import Data.List (nub)

import Utils
import Syntax.CommonTerm

------------------------------------------------------------------------------
-- Type Variables and Names
------------------------------------------------------------------------------

-- | Type variables
newtype TVar = MkTVar { tvar_name :: String } deriving (Eq, Show, Ord)

-- | Name of nominal type
newtype TypeName = MkTypeName { unTypeName :: String } deriving (Eq, Show, Ord)

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

------------------------------------------------------------------------------
-- Tags
------------------------------------------------------------------------------

data DataCodata = Data | Codata deriving (Eq, Ord, Show)

data DataCodataRep (dc :: DataCodata) where
  DataRep :: DataCodataRep Data
  CodataRep :: DataCodataRep Codata
deriving instance Show (DataCodataRep pol)
deriving instance Eq (DataCodataRep pol)
deriving instance Ord (DataCodataRep pol)

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

data TypArgs (pol :: Polarity) = MkTypArgs
  { prdTypes :: [Typ pol]
  , cnsTypes :: [Typ (FlipPol pol)]
  }

deriving instance Eq (TypArgs Pos)
deriving instance Eq (TypArgs Neg)
deriving instance Ord (TypArgs Pos)
deriving instance Ord (TypArgs Neg)

data XtorSig (pol :: Polarity) = MkXtorSig
  { sig_name :: XtorName
  , sig_args :: TypArgs pol
  }

deriving instance Eq (XtorSig Pos)
deriving instance Eq (XtorSig Neg)
deriving instance Ord (XtorSig Pos)
deriving instance Ord (XtorSig Neg)

data Typ (pol :: Polarity) where
  TyVar :: PolarityRep pol -> TVar -> Typ pol
  -- | We have to duplicate TyStructData and TyStructCodata here due to restrictions of the deriving mechanism of Haskell.
  TyData   :: PolarityRep pol ->  [XtorSig pol]   -> Typ pol
  TyCodata :: PolarityRep pol ->  [XtorSig (FlipPol pol)] -> Typ pol
  TyNominal :: PolarityRep pol -> TypeName -> Typ pol
  -- | PosRep = Union, NegRep = Intersection
  TySet :: PolarityRep pol -> [Typ pol] -> Typ pol
  TyRec :: PolarityRep pol -> TVar -> Typ pol -> Typ pol

deriving instance Eq (Typ Pos)
deriving instance Eq (Typ Neg)
deriving instance Ord (Typ Pos)
deriving instance Ord (Typ Neg)

getPolarity :: Typ pol -> PolarityRep pol
getPolarity (TyVar rep _)     = rep
getPolarity (TyData rep _)    = rep
getPolarity (TyCodata rep _)  = rep
getPolarity (TyNominal rep _) = rep
getPolarity (TySet rep _)     = rep
getPolarity (TyRec rep _ _)   = rep

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

freeTypeVars :: Typ pol -> [TVar]
freeTypeVars = nub . freeTypeVars'
  where
    freeTypeVars' :: Typ pol -> [TVar]
    freeTypeVars' (TyVar _ tv) = [tv]
    freeTypeVars' (TySet _ ts) = concat $ map freeTypeVars' ts
    freeTypeVars' (TyRec _ v t)  = filter (/= v) (freeTypeVars' t)
    freeTypeVars' (TyNominal _ _) = []
    freeTypeVars' (TyData _ xtors) = concat (map freeTypeVarsXtorSig  xtors)
    freeTypeVars' (TyCodata _ xtors) = concat (map freeTypeVarsXtorSig  xtors)

    freeTypeVarsXtorSig :: XtorSig pol -> [TVar]
    freeTypeVarsXtorSig (MkXtorSig _ (MkTypArgs prdTypes cnsTypes)) =
      concat (map freeTypeVars' prdTypes ++ map freeTypeVars' cnsTypes)


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
substituteType m var@(TyVar PosRep tv) =
  case M.lookup tv m of
    Nothing -> var
    Just (ty,_) -> ty
substituteType m var@(TyVar NegRep tv) =
  case M.lookup tv m of
    Nothing -> var
    Just (_,ty) -> ty
-- Other cases
substituteType m (TyData polrep args) = TyData polrep (substituteXtorSig m <$> args)
substituteType m (TyCodata polrep args) = TyCodata polrep (substituteXtorSig m <$> args)
substituteType _ ty@(TyNominal _ _) = ty
substituteType m (TySet rep args) = TySet rep (substituteType m <$> args)
substituteType m (TyRec rep tv arg) = TyRec rep tv (substituteType m arg)

substituteXtorSig :: Map TVar (Typ Pos, Typ Neg) -> XtorSig pol -> XtorSig pol
substituteXtorSig m MkXtorSig { sig_name, sig_args } =  MkXtorSig sig_name (substituteTypeArgs m sig_args)

substituteTypeArgs :: Map TVar (Typ Pos, Typ Neg) -> TypArgs pol -> TypArgs pol
substituteTypeArgs m MkTypArgs { prdTypes, cnsTypes } =
  MkTypArgs (substituteType m <$> prdTypes) (substituteType m <$> cnsTypes)

------------------------------------------------------------------------------
-- Constraints
------------------------------------------------------------------------------

data ConstraintInfo = Primary Loc | Derived | Recursive

data Constraint a = SubType a (Typ Pos) (Typ Neg)
  deriving (Eq, Ord, Functor)


-- | A ConstraintSet is a set of constraints, together with a list of all the
-- unification variables occurring in them.
data ConstraintSet a = ConstraintSet { cs_constraints :: [Constraint a]
                                     , cs_uvars :: [TVar]
                                     } deriving (Eq, Functor)

------------------------------------------------------------------------------
-- VariableState and SolverResult
------------------------------------------------------------------------------

data VariableState = VariableState
  { vst_upperbounds :: [Typ Neg]
  , vst_lowerbounds :: [Typ Pos] }

emptyVarState :: VariableState
emptyVarState = VariableState [] []

type SolverResult = Map TVar VariableState

------------------------------------------------------------------------------
-- Data Type declarations
------------------------------------------------------------------------------

data DataDecl = NominalDecl
  { data_name :: TypeName
  , data_polarity :: DataCodata
  , data_xtors :: [XtorSig Pos]
  }
  deriving (Eq)

