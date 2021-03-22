module Syntax.Types where

import Data.Map (Map)
import qualified Data.Map as M
import Data.List (nub)

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

data TVarKind = Normal | Recursive deriving (Eq, Show, Ord)

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

getPolarity :: Typ pol -> PolarityRep pol
getPolarity (TyVar rep _ _)        = rep
getPolarity (TyStructural rep _ _) = rep
getPolarity (TyNominal rep _)      = rep
getPolarity (TySet rep _)          = rep
getPolarity (TyRec rep _ _)        = rep

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
-- Substitution
------------------------------------------------------------------------------

-- This is probably not 100% correct w.r.t alpha-renaming. Postponed until we have a better repr. of types.
unfoldRecType :: Typ pol -> Typ pol
unfoldRecType recty@(TyRec PosRep var ty) = substituteType' Recursive (M.fromList [(var,(recty, undefined))]) ty
unfoldRecType recty@(TyRec NegRep var ty) = substituteType' Recursive (M.fromList [(var,(undefined,recty))]) ty
unfoldRecType ty = ty

substituteType' :: TVarKind -> Map TVar (Typ Pos, Typ Neg) -> Typ pol -> Typ pol
substituteType' Recursive m (TyVar PosRep Recursive tv) =
  case M.lookup tv m of
    Nothing -> (TyVar PosRep Recursive tv)
    Just (ty,_) -> ty
substituteType' Recursive m (TyVar NegRep Recursive tv) =
  case M.lookup tv m of
    Nothing -> (TyVar NegRep Recursive tv)
    Just (_,ty) -> ty
substituteType' Normal _ ty@(TyVar _ Recursive _) = ty
-- Normal Type Variables
substituteType' Normal m (TyVar PosRep Normal tv) =
  case M.lookup tv m of
    Nothing -> (TyVar PosRep Normal tv)
    Just (ty,_) -> ty
substituteType' Normal m (TyVar NegRep Normal tv) =
  case M.lookup tv m of
    Nothing -> (TyVar NegRep Normal tv)
    Just (_,ty) -> ty
substituteType' Recursive _ ty@(TyVar _ Normal _) = ty
-- Other cases
substituteType' k m (TyStructural polrep dcrep args) = TyStructural polrep dcrep (substituteXtorSig k m <$> args)
substituteType' _ _ ty@(TyNominal _ _) = ty
substituteType' k m (TySet rep args) = TySet rep (substituteType' k m <$> args)
substituteType' k m (TyRec rep tv arg) = TyRec rep tv (substituteType' k m arg)

substituteXtorSig :: TVarKind -> Map TVar (Typ Pos, Typ Neg) -> XtorSig pol -> XtorSig pol
substituteXtorSig k m MkXtorSig { sig_name, sig_args } =  MkXtorSig sig_name (substituteTypeArgs k m sig_args)

substituteTypeArgs :: TVarKind -> Map TVar (Typ Pos, Typ Neg) -> TypArgs pol -> TypArgs pol
substituteTypeArgs k m MkTypArgs { prdTypes, cnsTypes } =
  MkTypArgs (substituteType' k m <$> prdTypes) (substituteType' k m <$> cnsTypes)

substituteType :: Map TVar (Typ Pos, Typ Neg) -> Typ pol -> Typ pol
substituteType = substituteType' Normal

------------------------------------------------------------------------------
-- Constraints
------------------------------------------------------------------------------

data Constraint = SubType (Typ Pos) (Typ Neg) deriving (Eq, Ord)


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

