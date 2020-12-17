module Syntax.Types where

import Data.List (nub)

import Syntax.Terms
import Utils
import Data.Kind (Type)
import Data.Void

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

-- Free type variable.
newtype TVar = MkTVar { tvar_name :: String } deriving (Eq, Ord, Show)

-- Bound type variable.
newtype UVar = MkUVar {uvar_id :: Int} deriving (Eq,Ord, Show)

-- Name of nominal type.
data TypeName = MkTypeName { unTypeName :: String } deriving (Eq, Show, Ord)

data DataCodata = Data  | Codata  deriving (Eq, Show, Ord)

data UnionInter = Union | Inter deriving (Eq, Show)

data SimpleTarget = Simple | Target

type family TargetF (k :: SimpleTarget) :: Type where
  TargetF Target = ()
  TargetF Simple = Void

data XtorSig a = MkXtorSig { sig_name :: XtorName, sig_args :: Twice [a] }
  deriving (Show, Eq)

data Typ a
  = TyFreeVar TVar
  | TyBoundVar UVar
  | TySimple DataCodata [XtorSig (Typ a)]
  | TyNominal TypeName
  | TySet (TargetF a) UnionInter [Typ a]
  | TyRec (TargetF a) (Typ a)

type SimpleType = Typ Simple
type TargetType' = Typ Target

deriving instance Eq SimpleType
deriving instance Show SimpleType

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
-- Most of the stuff below is deprecated, and will be merged with
-- the stuff declared above.
------------------------------------------------------------------------------

switchPrdCns :: PrdCns -> PrdCns
switchPrdCns Cns = Prd
switchPrdCns Prd = Cns

applyVariance :: DataCodata -> PrdCns -> (PrdCns -> PrdCns)
applyVariance Data Prd = id
applyVariance Data Cns = switchPrdCns
applyVariance Codata Prd = switchPrdCns
applyVariance Codata Cns = id

alphaRenameTVar :: [TVar] -> TVar -> TVar
alphaRenameTVar tvs tv
  | tv `elem` tvs = head [newtv | n <- [(0 :: Integer)..], let newtv = MkTVar (tvar_name tv ++ show n), not (newtv `elem` tvs)]
  | otherwise = tv

-- bound type variables (used in recursive types)
newtype RVar = MkRVar { rvar_name :: String } deriving (Eq, Ord, Show)

data TargetType
  = TTySet UnionInter  [TargetType]
  | TTyTVar TVar
  | TTyRVar RVar
  | TTyRec RVar TargetType
  | TTySimple DataCodata [XtorSig TargetType]
  | TTyNominal TypeName
  deriving (Eq,Show)

-- replaces all free type variables in the type, so that they don't intersect with the given type variables
alphaRenameTargetType :: [TVar] -> TargetType -> TargetType
alphaRenameTargetType tvs (TTyTVar tv)   = TTyTVar (alphaRenameTVar tvs tv)
alphaRenameTargetType _   (TTyRVar rv)   = TTyRVar rv
alphaRenameTargetType tvs (TTySet ui tys) = TTySet ui (map (alphaRenameTargetType tvs) tys)
alphaRenameTargetType tvs (TTyRec rv ty) = TTyRec rv (alphaRenameTargetType tvs ty)
alphaRenameTargetType _ (TTyNominal tn) = TTyNominal tn
alphaRenameTargetType tvs (TTySimple s sigs) = TTySimple s $ map renameXtorSig  sigs
  where
    renameXtorSig (MkXtorSig xt args) = MkXtorSig xt (twiceMap (map (alphaRenameTargetType tvs)) (map (alphaRenameTargetType tvs)) args)

data TypeScheme = TypeScheme { ts_vars :: [TVar], ts_monotype :: TargetType } deriving (Show, Eq)

-- renames free variables of a type scheme, so that they don't intersect with the given list
alphaRenameTypeScheme :: [TVar] -> TypeScheme -> TypeScheme
alphaRenameTypeScheme tvs (TypeScheme tvs' ty) = TypeScheme (map (alphaRenameTVar tvs) tvs') (alphaRenameTargetType tvs ty)

unionOrInter :: PrdCns -> [TargetType] -> TargetType
unionOrInter _ [t] = t
unionOrInter Prd tys = TTySet Union tys
unionOrInter Cns tys = TTySet Inter tys

freeTypeVars' :: TargetType -> [TVar]
freeTypeVars' (TTyTVar tv) = [tv]
freeTypeVars' (TTyRVar _)  = []
freeTypeVars' (TTySet _ ts) = concat $ map freeTypeVars' ts
freeTypeVars' (TTyRec _ t)  = freeTypeVars' t
freeTypeVars' (TTyNominal _) = []
freeTypeVars' (TTySimple _ xtors) = concat (map freeTypeVarsXtorSig  xtors)
  where
    freeTypeVarsXtorSig (MkXtorSig _ (Twice prdTypes cnsTypes)) =
      concat (map freeTypeVars' prdTypes ++ map freeTypeVars' cnsTypes)

freeTypeVars :: TargetType -> [TVar]
freeTypeVars = nub . freeTypeVars'

-- generalizes over all free type variables of a type
generalize :: TargetType -> TypeScheme
generalize ty = TypeScheme (freeTypeVars ty) ty


