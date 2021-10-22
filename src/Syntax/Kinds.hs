module Syntax.Kinds where

import Data.Text (Text)

------------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------------

-- | An evaluation order is either call-by-value or call-by-name.
data CallingConvention
  = CBV -- ^ Call-by-value
  | CBN -- ^ Call-by-name
  deriving (Show, Eq, Ord)

-- | Kind variable
newtype KVar = MkKVar { unKVar :: Text }
  deriving (Show, Eq, Ord)

-- | We use the "Kinds are calling-conventions" approach to track
-- calling conventions at the type level.
-- Kind Variables are necessary during type inference, but we don't support
-- kind polymorphism.
data Kind = MonoKind CallingConvention
          | KindVar KVar
  deriving (Show, Eq, Ord)
