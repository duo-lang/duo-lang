module Syntax.Common.Kinds where

import Data.Set (Set)
import Data.Set qualified as S
import Syntax.Primitives
import Syntax.Common.Names



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

-- | An evaluation order is either call-by-value or call-by-name.
data EvaluationOrder = CBV | CBN
  deriving (Show, Eq, Ord)

-- | A calling convention is either boxed CBV/CBN or specific to a primitive type
data CallingConvention
  = CBox EvaluationOrder  -- ^ Boxed CBV/CBN
  | CRep PrimitiveType    -- ^ Primitive type representation
  deriving (Show, Eq, Ord)

------------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------------

evalOrder :: CallingConvention -> EvaluationOrder
evalOrder (CBox o) = o
evalOrder (CRep _) = CBV

-- | We use the "Kinds are calling-conventions" approach to track
-- calling conventions at the type level.
data Kind = MonoKind CallingConvention
  deriving (Show, Eq, Ord)
