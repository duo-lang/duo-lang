module Syntax.Types where

import Data.Map (Map)
import Data.Bifunctor (bimap)
import Data.List (nub)

import Syntax.Terms
import Utils

------------------------------------------------------------------------------
-- Type syntax
------------------------------------------------------------------------------

newtype UVar = MkUVar {uvar_id :: Int} deriving (Eq,Ord)

instance Show UVar where
  show (MkUVar i) = "U" ++ show i

data Polarity = Pos | Neg deriving (Show,Eq,Ord)

switchPolarity :: Polarity -> Polarity
switchPolarity Neg = Pos
switchPolarity Pos = Neg

applyVariance :: DataOrCodata -> PrdOrCns -> (Polarity -> Polarity)
applyVariance Data Prd = id
applyVariance Data Cns = switchPolarity
applyVariance Codata Prd = switchPolarity
applyVariance Codata Cns = id

type XtorSig a = (XtorName, Twice [a])

data SimpleType =
    TyVar UVar
  | SimpleType DataOrCodata [XtorSig SimpleType]
  deriving (Show,Eq)

data Constraint = SubType SimpleType SimpleType deriving (Eq, Show)

-- free type variables
newtype TVar = MkTVar { tvar_name :: String } deriving (Eq, Ord, Show)

alphaRenameTVar :: [TVar] -> TVar -> TVar
alphaRenameTVar tvs tv
  | tv `elem` tvs = head [newtv | n <- [0..], let newtv = MkTVar (tvar_name tv ++ show n), not (newtv `elem` tvs)]
  | otherwise = tv

-- bound type variables (used in recursive types)
newtype RVar = MkRVar { rvar_name :: String } deriving (Eq, Ord, Show)

data TargetType
  = TTyUnion [TargetType]
  | TTyInter [TargetType]
  | TTyTVar TVar
  | TTyRVar RVar
  | TTyRec RVar TargetType
  | TTySimple DataOrCodata [XtorSig TargetType]
  deriving (Eq,Show)

-- replaces all free type variables in the type, so that they don't intersect with the given type variables
alphaRenameTargetType :: [TVar] -> TargetType -> TargetType
alphaRenameTargetType tvs (TTyTVar tv)   = TTyTVar (alphaRenameTVar tvs tv)
alphaRenameTargetType _   (TTyRVar rv)   = TTyRVar rv
alphaRenameTargetType tvs (TTyUnion tys) = TTyUnion (map (alphaRenameTargetType tvs) tys)
alphaRenameTargetType tvs (TTyInter tys) = TTyInter (map (alphaRenameTargetType tvs) tys)
alphaRenameTargetType tvs (TTyRec rv ty) = TTyRec rv (alphaRenameTargetType tvs ty)
alphaRenameTargetType tvs (TTySimple s sigs) = TTySimple s $ map (bimap id (twiceMap (map (alphaRenameTargetType tvs)) (map (alphaRenameTargetType tvs)))) sigs

data TypeScheme = TypeScheme { ts_vars :: [TVar], ts_monotype :: TargetType }

-- renames free variables of a type scheme, so that they don't intersect with the given list
alphaRenameTypeScheme :: [TVar] -> TypeScheme -> TypeScheme
alphaRenameTypeScheme tvs (TypeScheme tvs' ty) = TypeScheme (map (alphaRenameTVar tvs) tvs') (alphaRenameTargetType tvs ty)

unionOrInter :: Polarity -> [TargetType] -> TargetType
unionOrInter _ [t] = t
unionOrInter Pos tys = TTyUnion tys
unionOrInter Neg tys = TTyInter tys

freeTypeVars' :: TargetType -> [TVar]
freeTypeVars' (TTyTVar tv) = [tv]
freeTypeVars' (TTyRVar _)  = []
freeTypeVars' (TTyUnion ts) = concat $ map freeTypeVars' ts
freeTypeVars' (TTyInter ts) = concat $ map freeTypeVars' ts
freeTypeVars' (TTyRec _ t)  = freeTypeVars' t
freeTypeVars' (TTySimple _ xtors) = concat (map (\(_,Twice prdTypes cnsTypes) -> concat (map freeTypeVars' prdTypes ++ map freeTypeVars' cnsTypes)) xtors)

freeTypeVars :: TargetType -> [TVar]
freeTypeVars = nub . freeTypeVars'

-- generalizes over all free type variables of a type
generalize :: TargetType -> TypeScheme
generalize ty = TypeScheme (freeTypeVars ty) ty

type TypeEnvironment = Map TypeIdentifierName TypeScheme
