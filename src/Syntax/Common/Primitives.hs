module Syntax.Common.Primitives where

import Data.Map (Map, fromList)
import Syntax.Common.PrdCns

-- | A primitive type/calling convention
data PrimitiveType =
      I64 -- ^ Primitive signed 64-bit integer
    | F64 -- ^ Primitive double-precision floating point
    | PChar
    | PString
    deriving (Show, Eq, Ord)

primTypeKeyword :: PrimitiveType -> String
primTypeKeyword I64 = "#I64"
primTypeKeyword F64 = "#F64"
primTypeKeyword PChar = "#Char"
primTypeKeyword PString = "#String"

data PrimitiveOp = Add | Sub | Mul | Div | Mod | Append | Prepend
  deriving (Show, Eq, Ord)

primOpKeyword :: PrimitiveOp -> String
primOpKeyword Add = "Add"
primOpKeyword Sub = "Sub"
primOpKeyword Mul = "Mul"
primOpKeyword Div = "Div"
primOpKeyword Mod = "Mod"
primOpKeyword Append = "Append"
primOpKeyword Prepend = "Prepend"

-- | Primitive operations and their arities
primOps :: Map (PrimitiveType, PrimitiveOp) Arity
primOps = fromList
  [
    -- I64
    ((I64, Add), [Prd, Prd, Cns]),
    ((I64, Sub), [Prd, Prd, Cns]),
    ((I64, Mul), [Prd, Prd, Cns]),
    ((I64, Div), [Prd, Prd, Cns]),
    ((I64, Mod), [Prd, Prd, Cns]),
    -- F64
    ((F64, Add), [Prd, Prd, Cns]),
    ((F64, Sub), [Prd, Prd, Cns]),
    ((F64, Mul), [Prd, Prd, Cns]),
    ((F64, Div), [Prd, Prd, Cns]),
    -- Char
    ((PChar, Prepend), [Prd, Prd, Cns]),
    -- String
    ((PString, Append), [Prd, Prd, Cns])
  ]
