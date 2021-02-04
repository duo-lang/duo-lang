module Syntax.Types where

import Data.Kind (Type)
import Data.List (nub)
import Data.Void

import Syntax.CommonTerm
import Utils

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

flipPol :: Polarity -> Polarity
flipPol Pos = Neg
flipPol Neg = Pos

type family FlipPol (pol :: Polarity) :: Polarity where
  FlipPol Pos = Neg
  FlipPol Neg = Pos

flipPolarityRep :: forall pol. PolarityRep pol -> PolarityRep (FlipPol pol)
flipPolarityRep PosRep = NegRep
flipPolarityRep NegRep = PosRep

data SomePol (f :: Polarity -> Type) where
  SomePos :: f Pos -> SomePol f
  SomeNeg :: f Neg -> SomePol f

------------------------------------------------------------------------------
-- Tags
------------------------------------------------------------------------------

data SimpleTarget = Simple | Target deriving (Eq, Ord, Show)

-- | Singleton Type for SimpleTarget
data SimpleTargetRep st where
  SimpleRep :: SimpleTargetRep Simple
  TargetRep :: SimpleTargetRep Target
deriving instance Show (SimpleTargetRep st)


data DataCodata = Data | Codata deriving (Eq, Ord, Show)

data UnionInter = Union | Inter deriving (Eq, Show, Ord)

data TVarKind = Normal | Recursive deriving (Eq, Show, Ord)

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

type family TargetF (k :: SimpleTarget) :: Type where
  TargetF Target = ()
  TargetF Simple = Void

data XtorSig a = MkXtorSig
  { sig_name :: XtorName
  , sig_args :: Twice [a]
  } deriving (Eq, Show, Ord)

data Typ a where
  TyVar :: TVarKind -> TVar -> Typ a
  TySimple :: DataCodata -> [XtorSig (Typ a)] -> Typ a
  TyNominal :: TypeName -> Typ a
  TySet :: TargetF a -> UnionInter -> [Typ a] -> Typ a
  TyRec :: TargetF a -> TVar -> Typ a -> Typ a

type SimpleType = Typ Simple
type TargetType = Typ Target

deriving instance Eq SimpleType
deriving instance Eq TargetType
deriving instance Show SimpleType
deriving instance Show TargetType
deriving instance Ord SimpleType
deriving instance Ord TargetType

------------------------------------------------------------------------------
-- Type Schemes
------------------------------------------------------------------------------

data TypeScheme = TypeScheme
  { ts_vars :: [TVar]
  , ts_monotype :: TargetType
  } deriving (Show, Eq)

freeTypeVars :: TargetType -> [TVar]
freeTypeVars = nub . freeTypeVars'
  where
    freeTypeVars' :: TargetType -> [TVar]
    freeTypeVars' (TyVar Normal tv) = [tv]
    freeTypeVars' (TyVar Recursive _)  = []
    freeTypeVars' (TySet () _ ts) = concat $ map freeTypeVars' ts
    freeTypeVars' (TyRec () _ t)  = freeTypeVars' t
    freeTypeVars' (TyNominal _) = []
    freeTypeVars' (TySimple _ xtors) = concat (map freeTypeVarsXtorSig  xtors)

    freeTypeVarsXtorSig :: XtorSig TargetType -> [TVar]
    freeTypeVarsXtorSig (MkXtorSig _ (Twice prdTypes cnsTypes)) =
      concat (map freeTypeVars' prdTypes ++ map freeTypeVars' cnsTypes)


-- | Generalize over all free type variables of a type.
generalize :: TargetType -> TypeScheme
generalize ty = TypeScheme (freeTypeVars ty) ty

------------------------------------------------------------------------------
-- Constraints
------------------------------------------------------------------------------

data Constraint = SubType SimpleType SimpleType deriving (Eq, Show, Ord)

-- | A ConstraintSet is a set of constraints, together with a list of all the
-- unification variables occurring in them.
data ConstraintSet = ConstraintSet { cs_constraints :: [Constraint]
                                   , cs_uvars :: [TVar]
                                   } deriving (Eq, Show)

------------------------------------------------------------------------------
-- Data Type declarations
------------------------------------------------------------------------------

data DataDecl = NominalDecl
  { data_name :: TypeName
  , data_polarity :: DataCodata
  , data_xtors :: [XtorSig SimpleType]
  }
  deriving (Show, Eq)

------------------------------------------------------------------------------
-- Helper Functions
------------------------------------------------------------------------------

switchPrdCns :: PrdCns -> PrdCns
switchPrdCns Cns = Prd
switchPrdCns Prd = Cns

applyVariance :: DataCodata -> PrdCns -> (PrdCns -> PrdCns)
applyVariance Data Prd = id
applyVariance Data Cns = switchPrdCns
applyVariance Codata Prd = switchPrdCns
applyVariance Codata Cns = id

unionOrInter :: PrdCns -> [TargetType] -> TargetType
unionOrInter _ [t] = t
unionOrInter Prd tys = TySet () Union tys
unionOrInter Cns tys = TySet () Inter tys

