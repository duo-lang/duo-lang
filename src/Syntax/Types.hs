module Syntax.Types where

import Data.Bifunctor (bimap)
import Data.List (nub)
import Data.Void
import Syntax.Terms
import Data.Kind (Type)
import Utils

------------------------------------------------------------------------------
-- Type Variables
------------------------------------------------------------------------------

newtype UVar = MkUVar {uvar_id :: Int} deriving (Eq,Ord)
instance Show UVar where
  show (MkUVar i) = "U" ++ show i

-- free type variables
newtype TVar = MkTVar { tvar_name :: String } deriving (Eq, Ord, Show)

-- bound type variables (used in recursive types)
newtype RVar = MkRVar { rvar_name :: String } deriving (Eq, Ord, Show)

------------------------------------------------------------------------------
-- New Type definition
------------------------------------------------------------------------------

data SimpleTarget = Simple | Target

type family TargetTypeF (st :: SimpleTarget) :: Type where
  TargetTypeF Simple = Void
  TargetTypeF Target = ()

type family SimpleTypeF (st :: SimpleTarget) :: Type where
  SimpleTypeF Simple = ()
  SimpleTypeF Target = Void

data Typ (st :: SimpleTarget) where
  -- Common for Simple and Target Types
  TySimple :: DataCodata -> [XtorSig (Typ st)] -> Typ st
  -- Just in Target Types
  TyUnion  :: TargetTypeF st -> [TargetType] -> Typ st
  TyInter  :: TargetTypeF st -> [TargetType] -> Typ st
  TyRec    :: TargetTypeF st -> RVar -> TargetType -> Typ st
  TyRVar   :: TargetTypeF st -> RVar -> Typ st
  TyTVar   :: TargetTypeF st -> TVar -> Typ st
  -- Just in Simple Types
  TyUVar   :: SimpleTypeF st -> UVar -> Typ st

deriving instance Show (Typ Simple)
deriving instance Show (Typ Target)
deriving instance Eq (Typ Simple)
deriving instance Eq (Typ Target)

type SimpleType = Typ Simple
type TargetType = Typ Target

------------------------------------------------------------------------------
-- Type syntax
------------------------------------------------------------------------------

data DataCodata
  = Data
  | Codata
  deriving (Eq, Show, Ord)





data Polarity = Pos | Neg deriving (Show,Eq,Ord)

switchPolarity :: Polarity -> Polarity
switchPolarity Neg = Pos
switchPolarity Pos = Neg

applyVariance :: DataCodata -> PrdCns -> (Polarity -> Polarity)
applyVariance Data Prd = id
applyVariance Data Cns = switchPolarity
applyVariance Codata Prd = switchPolarity
applyVariance Codata Cns = id

data XtorSig a = MkXtorSig { sig_name :: XtorName, sig_args :: Twice [a] }
  deriving (Show, Eq)

data Constraint = SubType SimpleType SimpleType deriving (Eq, Show)



alphaRenameTVar :: [TVar] -> TVar -> TVar
alphaRenameTVar tvs tv
  | tv `elem` tvs = head [newtv | n <- [0..], let newtv = MkTVar (tvar_name tv ++ show n), not (newtv `elem` tvs)]
  | otherwise = tv


-- replaces all free type variables in the type, so that they don't intersect with the given type variables
alphaRenameTargetType :: [TVar] -> TargetType -> TargetType
alphaRenameTargetType tvs (TyTVar () tv)   = TyTVar () (alphaRenameTVar tvs tv)
alphaRenameTargetType _   (TyRVar () rv)   = TyRVar () rv
alphaRenameTargetType tvs (TyUnion () tys) = TyUnion () (map (alphaRenameTargetType tvs) tys)
alphaRenameTargetType tvs (TyInter () tys) = TyInter ()(map (alphaRenameTargetType tvs) tys)
alphaRenameTargetType tvs (TyRec () rv ty) = TyRec () rv (alphaRenameTargetType tvs ty)
alphaRenameTargetType tvs (TySimple s sigs) = TySimple s $ map renameXtorSig  sigs
  where
    renameXtorSig (MkXtorSig xt args) = MkXtorSig xt (twiceMap (map (alphaRenameTargetType tvs)) (map (alphaRenameTargetType tvs)) args)

data TypeScheme = TypeScheme { ts_vars :: [TVar], ts_monotype :: TargetType } deriving (Show, Eq)

-- renames free variables of a type scheme, so that they don't intersect with the given list
alphaRenameTypeScheme :: [TVar] -> TypeScheme -> TypeScheme
alphaRenameTypeScheme tvs (TypeScheme tvs' ty) = TypeScheme (map (alphaRenameTVar tvs) tvs') (alphaRenameTargetType tvs ty)

unionOrInter :: Polarity -> [TargetType] -> TargetType
unionOrInter _ [t] = t
unionOrInter Pos tys = TyUnion () tys
unionOrInter Neg tys = TyInter () tys

freeTypeVars' :: TargetType -> [TVar]
freeTypeVars' (TyTVar () tv) = [tv]
freeTypeVars' (TyRVar ()  _)  = []
freeTypeVars' (TyUnion () ts) = concat $ map freeTypeVars' ts
freeTypeVars' (TyInter () ts) = concat $ map freeTypeVars' ts
freeTypeVars' (TyRec () _ t)  = freeTypeVars' t
freeTypeVars' (TySimple _ xtors) = concat (map freeTypeVarsXtorSig  xtors)
  where
    freeTypeVarsXtorSig (MkXtorSig _ (Twice prdTypes cnsTypes)) =
      concat (map freeTypeVars' prdTypes ++ map freeTypeVars' cnsTypes)

freeTypeVars :: TargetType -> [TVar]
freeTypeVars = nub . freeTypeVars'

-- generalizes over all free type variables of a type
generalize :: TargetType -> TypeScheme
generalize ty = TypeScheme (freeTypeVars ty) ty

