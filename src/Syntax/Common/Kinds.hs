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
-- Evaluation Order
---------------------------------------------------------------------------------

-- | An evaluation order is either call-by-value or call-by-name.
data EvaluationOrder = CBV | CBN
  deriving (Show, Eq, Ord)

---------------------------------------------------------------------------------
-- Calling Convention
---------------------------------------------------------------------------------

-- | A calling convention is either boxed CBV/CBN or specific to a primitive type
data CallingConvention
  = CBox EvaluationOrder  -- ^ Boxed CBV/CBN
  | CRep PrimitiveType    -- ^ Primitive type representation
  deriving (Show, Eq, Ord)

evalOrder :: CallingConvention -> EvaluationOrder
evalOrder (CBox o) = o
evalOrder (CRep _) = CBV

------------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------------

data PolyKind =
  MkPolyKind { contravariant :: [(TVar, Kind)]
             , covariant :: [(TVar, Kind)]
             , returnKind :: EvaluationOrder
             }

deriving instance (Show PolyKind)
deriving instance (Eq PolyKind)
allTypeVars :: PolyKind -> Set TVar
allTypeVars (MkPolyKind { contravariant, covariant }) =
  S.fromList ((fst <$> contravariant) ++ (fst <$> covariant))

-- | We use the "Kinds are calling-conventions" approach to track
-- calling conventions at the type level.
data Kind where
  MonoKind :: CallingConvention -> Kind
  deriving (Show, Eq, Ord)


