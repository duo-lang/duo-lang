module Syntax.Types where

import Data.Kind (Type)
import Data.List (nub)

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

data SomePol (f :: Polarity -> Type) where
  SomePos :: f Pos -> SomePol f
  SomeNeg :: f Neg -> SomePol f

------------------------------------------------------------------------------
-- Tags
------------------------------------------------------------------------------

data DataCodata = Data | Codata deriving (Eq, Ord, Show)

data TVarKind = Normal | Recursive deriving (Eq, Show, Ord)

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

data TypArgs (pol :: Polarity) = MkTypArgs
  { prdTypes :: [Typ pol]
  , cnsTypes :: [Typ pol]
  }

{-# DEPRECATED demote "This function will be removed once we have polar types" #-}
demote :: TypArgs pol -> Twice [Typ pol]
demote (MkTypArgs prdTypes cnsTypes) = Twice prdTypes cnsTypes

deriving instance Eq (TypArgs Pos)
deriving instance Eq (TypArgs Neg)
deriving instance Show (TypArgs Pos)
deriving instance Show (TypArgs Neg)
deriving instance Ord (TypArgs Pos)
deriving instance Ord (TypArgs Neg)

data XtorSig (pol :: Polarity) = MkXtorSig
  { sig_name :: XtorName
  , sig_args :: TypArgs pol
  }

deriving instance Eq (XtorSig Pos)
deriving instance Eq (XtorSig Neg)
deriving instance Show (XtorSig Pos)
deriving instance Show (XtorSig Neg)
deriving instance Ord (XtorSig Pos)
deriving instance Ord (XtorSig Neg)

data Typ (pol :: Polarity) where
  TyVar :: PolarityRep pol -> TVarKind -> TVar -> Typ pol
  TyStructural :: PolarityRep pol -> DataCodata -> [XtorSig pol] -> Typ pol
  TyNominal :: PolarityRep pol -> TypeName -> Typ pol
  -- | PosRep = Union, NegRep = Intersection
  TySet :: Polarity -> [Typ pol] -> Typ pol
  TyRec :: PolarityRep pol -> TVar -> Typ pol -> Typ pol

deriving instance Eq (Typ Pos)
deriving instance Eq (Typ Neg)
deriving instance Show (Typ Pos)
deriving instance Show (Typ Neg)
deriving instance Ord (Typ Pos)
deriving instance Ord (Typ Neg)

------------------------------------------------------------------------------
-- Type Schemes
------------------------------------------------------------------------------

data TypeScheme (pol :: Polarity) = TypeScheme
  { ts_vars :: [TVar]
  , ts_monotype :: Typ pol
  }

deriving instance Eq (TypeScheme Pos)
deriving instance Eq (TypeScheme Neg)
deriving instance Show (TypeScheme Pos)
deriving instance Show (TypeScheme Neg)
deriving instance Ord (TypeScheme Pos)
deriving instance Ord (TypeScheme Neg)

freeTypeVars :: Typ pol -> [TVar]
freeTypeVars = nub . freeTypeVars'
  where
    freeTypeVars' :: Typ pol -> [TVar]
    freeTypeVars' (TyVar _ Normal tv) = [tv]
    freeTypeVars' (TyVar _ Recursive _)  = []
    freeTypeVars' (TySet _ ts) = concat $ map freeTypeVars' ts
    freeTypeVars' (TyRec _ _ t)  = freeTypeVars' t
    freeTypeVars' (TyNominal _ _) = []
    freeTypeVars' (TyStructural _ _ xtors) = concat (map freeTypeVarsXtorSig  xtors)

    freeTypeVarsXtorSig :: XtorSig pol -> [TVar]
    freeTypeVarsXtorSig (MkXtorSig _ (MkTypArgs prdTypes cnsTypes)) =
      concat (map freeTypeVars' prdTypes ++ map freeTypeVars' cnsTypes)


-- | Generalize over all free type variables of a type.
generalize :: Typ pol -> TypeScheme pol
generalize ty = TypeScheme (freeTypeVars ty) ty

------------------------------------------------------------------------------
-- Constraints
------------------------------------------------------------------------------

data Constraint = SubType (Typ Pos) (Typ Pos) deriving (Eq, Show, Ord)

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
  , data_xtors :: [XtorSig Pos]
  }
  deriving (Show, Eq)

