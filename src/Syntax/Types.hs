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

data DataCodataRep (dc :: DataCodata) where
  DataRep :: DataCodataRep Data
  CodataRep :: DataCodataRep Codata
deriving instance Show (DataCodataRep pol)
deriving instance Eq (DataCodataRep pol)
deriving instance Ord (DataCodataRep pol)

data TVarKind = Normal | Recursive deriving (Eq, Show, Ord)

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

data TypArgs (pol :: Polarity) = MkTypArgs
  { prdTypes :: [Typ pol]
  , cnsTypes :: [Typ (FlipPol pol)]
  }

{-# DEPRECATED demote "This function will be removed once we have polar types" #-}
demote :: TypArgs pol -> Twice [Typ pol]
demote (MkTypArgs prdTypes _cnsTypes) = Twice prdTypes undefined -- cnsTypes

deriving instance Eq (TypArgs Pos)
deriving instance Eq (TypArgs Neg)
--deriving instance Show (TypArgs Pos)
--deriving instance Show (TypArgs Neg)
deriving instance Ord (TypArgs Pos)
deriving instance Ord (TypArgs Neg)

data XtorSig (pol :: Polarity) = MkXtorSig
  { sig_name :: XtorName
  , sig_args :: TypArgs pol
  }

deriving instance Eq (XtorSig Pos)
deriving instance Eq (XtorSig Neg)
--deriving instance Show (XtorSig Pos)
--deriving instance Show (XtorSig Neg)
deriving instance Ord (XtorSig Pos)
deriving instance Ord (XtorSig Neg)

type family XtorF (a :: Polarity) (b :: DataCodata) :: Polarity where
  XtorF Pos Data = Pos
  XtorF Pos Codata = Neg
  XtorF Neg Data = Neg
  XtorF Neg Codata = Pos

data Typ (pol :: Polarity) where
  TyVar :: PolarityRep pol -> TVarKind -> TVar -> Typ pol
  TyStructural :: PolarityRep pol -> DataCodataRep dc -> [XtorSig (XtorF pol dc)] -> Typ pol
  TyNominal :: PolarityRep pol -> TypeName -> Typ pol
  -- | PosRep = Union, NegRep = Intersection
  TySet :: PolarityRep pol -> [Typ pol] -> Typ pol
  TyRec :: PolarityRep pol -> TVar -> Typ pol -> Typ pol


getPolarityRep :: Typ pol -> PolarityRep pol
getPolarityRep (TyVar rep _ _) = rep
getPolarityRep (TyStructural rep _ _) = rep
getPolarityRep (TyNominal rep _) = rep
getPolarityRep (TySet rep _) = rep
getPolarityRep (TyRec rep _ _) = rep

-- | We need to write Eq and Ord instances by hand, due to the existential type variable dc in "TyStructural"
instance Eq (Typ Pos) where
  (TyVar PosRep Recursive tv) == (TyVar PosRep Recursive tv') = tv == tv'
  (TyVar PosRep Normal tv) == (TyVar PosRep Normal tv') = tv == tv'
  (TyStructural PosRep DataRep xtors) == (TyStructural PosRep DataRep xtors') = xtors == xtors'
  (TyStructural PosRep CodataRep xtors) == (TyStructural PosRep CodataRep xtors') = xtors == xtors'
  (TyNominal PosRep tn) == (TyNominal PosRep tn') = tn == tn'
  (TySet PosRep tys) == (TySet PosRep tys') = tys == tys'
  (TyRec PosRep v t) == (TyRec PosRep v' t') = v == v' && t == t'
  _ == _ = False
instance Eq (Typ Neg) where
  (TyVar NegRep Recursive tv) == (TyVar NegRep Recursive tv') = tv == tv'
  (TyVar NegRep Normal tv) == (TyVar NegRep Normal tv') = tv == tv'
  (TyStructural NegRep DataRep xtors) == (TyStructural NegRep DataRep xtors') = xtors == xtors'
  (TyStructural NegRep CodataRep xtors) == (TyStructural NegRep CodataRep xtors') = xtors == xtors'
  (TyNominal NegRep tn) == (TyNominal NegRep tn') = tn == tn'
  (TySet NegRep tys) == (TySet NegRep tys') = tys == tys'
  (TyRec NegRep v t) == (TyRec NegRep v' t') = v == v' && t == t'
  _ == _ = False

--deriving instance Show (Typ Pos)
--deriving instance Show (Typ Neg)

-- | Lexicographic ordering for two arguments
compare2 :: (Ord a, Ord b) => a -> a -> b -> b -> Ordering
compare2 x1 x2 y1 y2 = case x1 `compare` x2 of
  LT -> LT
  GT -> GT
  EQ -> y1 `compare` y2

instance Ord (Typ Pos) where
  -- Cases where same type constructor is used type constructor:
  (TyVar PosRep rn tv) `compare` (TyVar PosRep rn' tv') = compare2 rn rn' tv tv'
  (TyStructural PosRep dc xtors) `compare` (TyStructural PosRep dc' xtors') = case (dc,dc') of
    (DataRep,DataRep) -> xtors `compare` xtors'
    (CodataRep,CodataRep) -> xtors `compare` xtors'
    (DataRep, CodataRep) -> LT
    (CodataRep, DataRep) -> GT
  (TyNominal PosRep tn) `compare` (TyNominal PosRep tn') = tn `compare` tn'
  (TySet PosRep tys) `compare` (TySet PosRep tys') = tys `compare` tys'
  (TyRec PosRep v t) `compare` (TyRec PosRep v' t') = compare2 v v' t t'
  -- Cases where different constructors are used: TyVar < TyStructural < TyNominal < TySet < TyRec
  (TyVar _ _ _) `compare`_ = LT
  (TyStructural _ _ _) `compare` _ = LT
  (TyNominal _ _) `compare` _ = LT
  (TySet _ _) `compare` _ = LT
  (TyRec _ _ _) `compare` _ = GT

instance Ord (Typ Neg) where
  -- Cases where same type constructor is used type constructor:
  (TyVar NegRep rn tv) `compare` (TyVar NegRep rn' tv') = compare2 rn rn' tv tv'
  (TyStructural NegRep dc xtors) `compare` (TyStructural NegRep dc' xtors') = case (dc,dc') of
    (DataRep,DataRep) -> xtors `compare` xtors'
    (CodataRep,CodataRep) -> xtors `compare` xtors'
    (DataRep, CodataRep) -> LT
    (CodataRep, DataRep) -> GT
  (TyNominal NegRep tn) `compare` (TyNominal NegRep tn') = tn `compare` tn'
  (TySet NegRep tys) `compare` (TySet NegRep tys') = tys `compare` tys'
  (TyRec NegRep v t) `compare` (TyRec NegRep v' t') = compare2 v v' t t'
  -- Cases where different constructors are used: TyVar < TyStructural < TyNominal < TySet < TyRec
  (TyVar _ _ _) `compare`_ = LT
  (TyStructural _ _ _) `compare` _ = LT
  (TyNominal _ _) `compare` _ = LT
  (TySet _ _) `compare` _ = LT
  (TyRec _ _ _) `compare` _ = GT


------------------------------------------------------------------------------
-- Type Schemes
------------------------------------------------------------------------------

data TypeScheme (pol :: Polarity) = TypeScheme
  { ts_vars :: [TVar]
  , ts_monotype :: Typ pol
  }

deriving instance Eq (TypeScheme Pos)
deriving instance Eq (TypeScheme Neg)
--deriving instance Show (TypeScheme Pos)
--deriving instance Show (TypeScheme Neg)
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

data Constraint = SubType (Typ Pos) (Typ Pos) deriving (Eq, Ord)

-- | A ConstraintSet is a set of constraints, together with a list of all the
-- unification variables occurring in them.
data ConstraintSet = ConstraintSet { cs_constraints :: [Constraint]
                                   , cs_uvars :: [TVar]
                                   } deriving (Eq)

------------------------------------------------------------------------------
-- Data Type declarations
------------------------------------------------------------------------------

data DataDecl = NominalDecl
  { data_name :: TypeName
  , data_polarity :: DataCodata
  , data_xtors :: [XtorSig Pos]
  }
  deriving (Eq)

------------------------------------------------------------------------------
-- Helper Functions
------------------------------------------------------------------------------

applyVariance :: DataCodata -> Polarity -> (Polarity -> Polarity)
applyVariance Data Pos = id
applyVariance Data Neg = flipPol
applyVariance Codata Pos = flipPol
applyVariance Codata Neg = id

unionOrInter :: PolarityRep pol -> [Typ pol] -> (Typ pol)
unionOrInter _ [t] = t
unionOrInter rep tys = TySet rep tys


