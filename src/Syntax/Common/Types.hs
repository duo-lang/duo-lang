module Syntax.Common.Types where

import Data.Set (Set)
import Data.Set qualified as S

import Syntax.Kinds
import Syntax.Common.Names

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
  deriving (Eq, Show, Ord)

---------------------------------------------------------------------------------
-- TParams
---------------------------------------------------------------------------------

data TParams = MkTParams
  { contravariant :: [(TVar, Kind)],
    covariant :: [(TVar, Kind)]
  } deriving (Show)

allTypeVars :: TParams -> Set TVar
allTypeVars (MkTParams con cov) = S.fromList ((fst <$> con) ++ (fst <$> cov))

---------------------------------------------------------------------------------
-- Type Operators
---------------------------------------------------------------------------------

data BinOp where
  FunOp    :: BinOp
  ParOp    :: BinOp
  UnionOp  :: BinOp
  InterOp  :: BinOp
  deriving (Show, Eq)
