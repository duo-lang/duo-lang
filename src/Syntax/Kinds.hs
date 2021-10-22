module Syntax.Kinds where

import Data.Text (Text)

------------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------------

-- | An evaluation order is either call-by-value or call-by-name.
data EvalOrder
  = CBV -- ^ Call-by-value
  | CBN -- ^ Call-by-name
  deriving (Show, Eq)

-- | We use the "Kinds are calling-conventions" approach to track
-- calling conventions at the type level.
-- Kind Variables are necessary during type inference, but we don't support
-- kind polymorphism.
data Kind = MonoKind EvalOrder
          | KindVar Text
  deriving (Show, Eq)
