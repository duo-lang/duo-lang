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
-- MonoKind
---------------------------------------------------------------------------------

-- | A MonoKind is a kind which classifies inhabitated types.
data MonoKind
  = CBox EvaluationOrder  -- ^ Boxed CBV/CBN
  | CRep PrimitiveType    -- ^ Primitive type representation
  deriving (Show, Eq, Ord)

------------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------------

data PolyKind =
  MkPolyKind { contravariant :: [(TVar, MonoKind)]
             , covariant :: [(TVar, MonoKind)]
             , returnKind :: EvaluationOrder
             }

deriving instance (Show PolyKind)
deriving instance (Eq PolyKind)

allTypeVars :: PolyKind -> Set TVar
allTypeVars (MkPolyKind { contravariant, covariant }) =
  S.fromList ((fst <$> contravariant) ++ (fst <$> covariant))
