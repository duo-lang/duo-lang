module Syntax.Kinds where

import Syntax.Primitives

------------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------------

-- | An evaluation order is either call-by-value or call-by-name.
data EvaluationOrder = CBV | CBN
  deriving (Show, Eq, Ord)

-- | A calling convention is either boxed CBV/CBN or specific to a primitive type
data CallingConvention
  = CBox EvaluationOrder  -- ^ Boxed CBV/CBN
  | CRep PrimitiveType    -- ^ Primitive type representation
  deriving (Show, Eq, Ord)

evalOrder :: CallingConvention -> EvaluationOrder
evalOrder (CBox o) = o
evalOrder (CRep _) = CBV

-- | We use the "Kinds are calling-conventions" approach to track
-- calling conventions at the type level.
data Kind = MonoKind CallingConvention
  deriving (Show, Eq, Ord)
