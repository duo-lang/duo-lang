module Syntax.Common.Primitives where

import Syntax.Common.PrdCns ( Arity, PrdCns(..) )

-- | A primitive type/calling convention
data PrimitiveType =
      I64 -- ^ Primitive signed 64-bit integer
    | F64 -- ^ Primitive double-precision floating point
    | PChar
    | PString
    deriving (Show, Eq, Ord)

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


-- | Primitive operations and their arities
primOps :: PrimitiveOp -> Arity
-- I64
primOps I64Add = [Prd, Prd, Cns]
primOps I64Sub = [Prd, Prd, Cns]
primOps I64Mul = [Prd, Prd, Cns]
primOps I64Div = [Prd, Prd, Cns]
primOps I64Mod = [Prd, Prd, Cns]
-- F64
primOps F64Add = [Prd, Prd, Cns]
primOps F64Sub = [Prd, Prd, Cns]
primOps F64Mul = [Prd, Prd, Cns]
primOps F64Div = [Prd, Prd, Cns]
-- Char
primOps CharPrepend = [Prd, Prd, Cns]
-- String
primOps StringAppend = [Prd, Prd, Cns]

