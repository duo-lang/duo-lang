module Syntax.Kinds where

------------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------------

-- | An evaluation order is either call-by-value or call-by-name.
data CallingConvention
  = CBV -- ^ Call-by-value
  | CBN -- ^ Call-by-name
  deriving (Show, Eq, Ord)

-- | We use the "Kinds are calling-conventions" approach to track
-- calling conventions at the type level.
data Kind = MonoKind CallingConvention
  deriving (Show, Eq, Ord)
