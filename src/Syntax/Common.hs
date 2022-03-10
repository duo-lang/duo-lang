module Syntax.Common where

import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)

import Syntax.Kinds

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

---------------------------------------------------------------------------------
-- Phases
---------------------------------------------------------------------------------

data Phase where
  Parsed :: Phase
  Inferred :: Phase
  Compiled :: Phase
  deriving (Show, Eq, Ord)

---------------------------------------------------------------------------------
-- Producer/Consumer
---------------------------------------------------------------------------------

data PrdCns
  = Prd
  | Cns
  deriving (Eq, Show, Ord)

-- | Singleton Type for PrdCns
data PrdCnsRep pc where
  PrdRep :: PrdCnsRep Prd
  CnsRep :: PrdCnsRep Cns
deriving instance Show (PrdCnsRep pc)
deriving instance Eq (PrdCnsRep pc)

type family FlipPrdCns (pc :: PrdCns) :: PrdCns where
  FlipPrdCns Prd = Cns
  FlipPrdCns Cns = Prd

flipPrdCns :: PrdCnsRep pc -> PrdCnsRep (FlipPrdCns pc)
flipPrdCns PrdRep = CnsRep
flipPrdCns CnsRep = PrdRep

type family PrdCnsFlip (pc :: PrdCns) (pol :: Polarity) :: Polarity where
  PrdCnsFlip Prd pol = pol
  PrdCnsFlip Cns pol = FlipPol pol

-- | We map producer terms to positive types, and consumer terms to negative types.
type family PrdCnsToPol (pc :: PrdCns) :: Polarity where
  PrdCnsToPol Prd = Pos
  PrdCnsToPol Cns = Neg

prdCnsToPol :: PrdCnsRep pc -> PolarityRep (PrdCnsToPol pc)
prdCnsToPol PrdRep = PosRep
prdCnsToPol CnsRep = NegRep

------------------------------------------------------------------------------
-- Data/Codata
------------------------------------------------------------------------------

data DataCodata = Data | Codata deriving (Eq, Ord, Show)

data DataCodataRep (dc :: DataCodata) where
  DataRep :: DataCodataRep Data
  CodataRep :: DataCodataRep Codata

deriving instance Show (DataCodataRep pol)
deriving instance Eq (DataCodataRep pol)
deriving instance Ord (DataCodataRep pol)

---------------------------------------------------------------------------------
-- Nominal/Structural/Refinement
---------------------------------------------------------------------------------

data NominalStructural = Nominal | Structural | Refinement deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------
-- Refined / NotRefined
---------------------------------------------------------------------------------

data IsRefined = Refined | NotRefined
  deriving (Show, Ord, Eq)

---------------------------------------------------------------------------------
-- IsRec
---------------------------------------------------------------------------------

data IsRec = Recursive | NonRecursive deriving (Show, Eq, Ord)

---------------------------------------------------------------------------------
-- Variance
---------------------------------------------------------------------------------

data Variance = Covariant | Contravariant

---------------------------------------------------------------------------------
-- TParams
---------------------------------------------------------------------------------

data TParams = MkTParams
  { covariant :: [(TVar, Kind)]
  , contravariant :: [(TVar, Kind)]
  } deriving (Show)

allTypeVars :: TParams -> Set TVar
allTypeVars (MkTParams cov con) = S.fromList ((fst <$> cov) ++ (fst <$> con))

---------------------------------------------------------------------------------
-- Type Operators
---------------------------------------------------------------------------------

data BinOp where
  FunOp    :: BinOp
  ParOp    :: BinOp
  UnionOp  :: BinOp
  InterOp  :: BinOp
  deriving (Show, Eq)


---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

newtype ModuleName = ModuleName { unModuleName :: Text } deriving (Eq, Ord, Show)

-- | Name of a constructor/destructor. Starts with an uppercase letter.
newtype XtorName = MkXtorName { unXtorName :: Text } deriving (Eq, Ord, Show)

-- | Name of nominal type
newtype TypeName = MkTypeName { unTypeName :: Text } deriving (Eq, Show, Ord)

-- | Name of a free variable. Starts with a lowercase letter.
type FreeVarName = Text

-- | Type variables
newtype TVar = MkTVar { tvar_name :: Text } deriving (Eq, Show, Ord)

-- | Two-level de Bruijn indices.
type Index = (Int, Int)
