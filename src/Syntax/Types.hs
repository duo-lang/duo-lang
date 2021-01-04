module Syntax.Types where

import Data.List (nub)

import Syntax.Terms
import Utils

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

data SimpleType =
    TyVar UVar
  | SimpleType DataCodata [XtorSig SimpleType]
  | NominalType TypeName

  deriving (Show,Eq)

data Constraint = SubType SimpleType SimpleType deriving (Eq, Show)

-- free type variables
newtype TVar = MkTVar { tvar_name :: String } deriving (Eq, Ord, Show)

-- bound type variables (used in recursive types)
newtype RVar = MkRVar { rvar_name :: String } deriving (Eq, Ord, Show)

data TargetType
  = TTySet UnionInter [TargetType]
  | TTyTVar TVar
  | TTyRVar RVar
  | TTyRec RVar TargetType
  | TTySimple DataCodata [XtorSig TargetType]
  | TTyNominal TypeName
  deriving (Eq,Show)

data TypeScheme = TypeScheme { ts_vars :: [TVar], ts_monotype :: TargetType } deriving (Show, Eq)

unionOrInter :: PrdCns -> [TargetType] -> TargetType
unionOrInter _ [t] = t
unionOrInter Prd tys = TTySet Union tys
unionOrInter Cns tys = TTySet Inter tys



freeTypeVars :: TargetType -> [TVar]
freeTypeVars = nub . freeTypeVars'
  where
    freeTypeVars' :: TargetType -> [TVar]
    freeTypeVars' (TTyTVar tv) = [tv]
    freeTypeVars' (TTyRVar _)  = []
    freeTypeVars' (TTySet _ ts) = concat $ map freeTypeVars' ts
    freeTypeVars' (TTyRec _ t)  = freeTypeVars' t
    freeTypeVars' (TTyNominal _) = []
    freeTypeVars' (TTySimple _ xtors) = concat (map freeTypeVarsXtorSig  xtors)

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
