module Syntax.Types where

import Data.Kind (Type)
import Data.List (nub)
import Data.Void

import Syntax.Terms
import Utils

------------------------------------------------------------------------------
-- Type Variables and Names
------------------------------------------------------------------------------

-- | Unification Variables
newtype UVar = MkUVar { uvar_id :: Int } deriving (Eq, Show, Ord)

-- | Type variables
newtype TVar = MkTVar { tvar_name :: String } deriving (Eq, Show, Ord)

-- | Name of nominal type
newtype TypeName = MkTypeName { unTypeName :: String } deriving (Eq, Show, Ord)

------------------------------------------------------------------------------
-- Tags
------------------------------------------------------------------------------

data SimpleTarget = Simple | Target deriving (Eq, Ord, Show)

data DataCodata = Data | Codata deriving (Eq, Ord, Show)

data UnionInter = Union | Inter deriving (Eq, Show, Ord)

data TVarKind = Normal | Recursive deriving (Eq, Show, Ord)

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

type family TargetF (k :: SimpleTarget) :: Type where
  TargetF Target = ()
  TargetF Simple = Void

type family SimpleF (k :: SimpleTarget) :: Type where
  SimpleF Target = Void
  SimpleF Simple = ()

data XtorSig a = MkXtorSig
  { sig_name :: XtorName
  , sig_args :: Twice [a]
  } deriving (Eq, Show)

data Typ a
  = TyTVar (TargetF a) TVarKind TVar
  | TyUVar (SimpleF a) UVar
  | TySimple DataCodata [XtorSig (Typ a)]
  | TyNominal TypeName
  | TySet (TargetF a) UnionInter [Typ a]
  | TyRec (TargetF a) TVar (Typ a)

type SimpleType = Typ Simple
type TargetType = Typ Target

deriving instance Eq SimpleType
deriving instance Eq TargetType
deriving instance Show SimpleType
deriving instance Show TargetType

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
    freeTypeVars' (TyTVar () Normal tv) = [tv]
    freeTypeVars' (TyTVar () Recursive _)  = []
    freeTypeVars' (TyUVar v _) = absurd v
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

data Constraint = SubType SimpleType SimpleType deriving (Eq, Show)

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

