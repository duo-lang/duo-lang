module Syntax.Primitives where

-- | A primitive type/calling convention
data PrimitiveType =
      I64 -- ^ PrimitiveType signed 64-bit integer
    | F64 -- ^ PrimitiveType double-precision floating point
    deriving (Show, Eq, Ord)

-- | A primitive literal
data PrimitiveLiteral =
      I64Lit Integer
    | F64Lit Double
    deriving (Show, Eq, Ord)

typeOfLiteral :: PrimitiveLiteral -> PrimitiveType
typeOfLiteral (I64Lit _) = I64
typeOfLiteral (F64Lit _) = F64
