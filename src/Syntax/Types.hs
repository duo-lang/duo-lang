module Syntax.Types where

import Data.List (nub)
import Data.Kind (Type)
import Data.Void

import Syntax.Terms
import Utils


------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

data SimpleTarget = Simple | Target

type family TargetF (k :: SimpleTarget) :: Type where
  TargetF Target = ()
  TargetF Simple = Void

type family SimpleF (k :: SimpleTarget) :: Type where
  SimpleF Target = Void
  SimpleF Simple = ()

data Typ a
  = TyTVar (TargetF a) TVar
  | TyRVar (TargetF a) RVar
  | TyUVar (SimpleF a) UVar
  | TySimple DataCodata [XtorSig (Typ a)]
  | TyNominal TypeName
  | TySet (TargetF a) UnionInter [Typ a]
  | TyRec (TargetF a) RVar (Typ a)

type SimpleType = Typ Simple
type TargetType = Typ Target

deriving instance Eq SimpleType
deriving instance Eq TargetType
deriving instance Show SimpleType
deriving instance Show TargetType

------------------------------------------------------------------------------
-- Type syntax
------------------------------------------------------------------------------


data TypeName = MkTypeName { unTypeName :: String } deriving (Eq, Show, Ord)

data DataCodata
  = Data
  | Codata
  deriving (Eq, Show, Ord)

data UnionInter = Union | Inter deriving (Eq, Show, Ord)

newtype UVar = MkUVar {uvar_id :: Int} deriving (Eq,Ord)

instance Show UVar where
  show (MkUVar i) = "U" ++ show i

switchPrdCns :: PrdCns -> PrdCns
switchPrdCns Cns = Prd
switchPrdCns Prd = Cns

applyVariance :: DataCodata -> PrdCns -> (PrdCns -> PrdCns)
applyVariance Data Prd = id
applyVariance Data Cns = switchPrdCns
applyVariance Codata Prd = switchPrdCns
applyVariance Codata Cns = id

data XtorSig a = MkXtorSig { sig_name :: XtorName, sig_args :: Twice [a] }
  deriving (Show, Eq)

data Constraint = SubType SimpleType SimpleType deriving (Eq, Show)

-- free type variables
newtype TVar = MkTVar { tvar_name :: String } deriving (Eq, Ord, Show)

-- bound type variables (used in recursive types)
newtype RVar = MkRVar { rvar_name :: String } deriving (Eq, Ord, Show)

data TypeScheme = TypeScheme { ts_vars :: [TVar], ts_monotype :: TargetType } deriving (Show, Eq)

unionOrInter :: PrdCns -> [TargetType] -> TargetType
unionOrInter _ [t] = t
unionOrInter Prd tys = TySet () Union tys
unionOrInter Cns tys = TySet () Inter tys



freeTypeVars :: TargetType -> [TVar]
freeTypeVars = nub . freeTypeVars'
  where
    freeTypeVars' :: TargetType -> [TVar]
    freeTypeVars' (TyTVar () tv) = [tv]
    freeTypeVars' (TyRVar () _)  = []
    freeTypeVars' (TyUVar v _) = absurd v
    freeTypeVars' (TySet () _ ts) = concat $ map freeTypeVars' ts
    freeTypeVars' (TyRec () _ t)  = freeTypeVars' t
    freeTypeVars' (TyNominal _) = []
    freeTypeVars' (TySimple _ xtors) = concat (map freeTypeVarsXtorSig  xtors)

    freeTypeVarsXtorSig :: XtorSig TargetType -> [TVar]
    freeTypeVarsXtorSig (MkXtorSig _ (Twice prdTypes cnsTypes)) =
      concat (map freeTypeVars' prdTypes ++ map freeTypeVars' cnsTypes)


-- generalizes over all free type variables of a type
generalize :: TargetType -> TypeScheme
generalize ty = TypeScheme (freeTypeVars ty) ty

------------------------------------------------------------------------------
-- Data Type declarations
------------------------------------------------------------------------------

data DataDecl = NominalDecl
  { data_name :: TypeName
  , data_polarity :: DataCodata
  , data_xtors :: [XtorSig SimpleType]
  }
  deriving (Show, Eq)
