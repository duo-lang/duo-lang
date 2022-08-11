module Syntax.Common.Primitives
  ( PrimitiveOp(..)
  ) where

data PrimitiveOp where
  -- I64 Ops
  I64Add :: PrimitiveOp
  I64Sub :: PrimitiveOp
  I64Mul :: PrimitiveOp
  I64Div :: PrimitiveOp
  I64Mod :: PrimitiveOp
  -- F64 Ops
  F64Add :: PrimitiveOp
  F64Sub :: PrimitiveOp
  F64Mul :: PrimitiveOp
  F64Div :: PrimitiveOp
  -- Char Ops
  CharPrepend :: PrimitiveOp
  -- String Ops
  StringAppend :: PrimitiveOp
  deriving (Show, Eq, Ord, Enum, Bounded)

