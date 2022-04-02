module TypeInference.GenerateConstraints.Primitives where

import Data.Map

import Syntax.Common
import Syntax.RST.Types

simplePrimBinOp :: PrimitiveType -> LinearContext Neg
simplePrimBinOp pt = [PrdCnsType PrdRep (TyPrim NegRep pt), PrdCnsType PrdRep (TyPrim NegRep pt), PrdCnsType CnsRep (TyPrim PosRep pt)]

-- | Primitive operations and their signatures
primOps :: Map (PrimitiveType, PrimitiveOp) (LinearContext Neg)
primOps = fromList
  [
    -- I64
    ((I64, Add), simplePrimBinOp I64),
    ((I64, Sub), simplePrimBinOp I64),
    ((I64, Mul), simplePrimBinOp I64),
    ((I64, Div), simplePrimBinOp I64),
    ((I64, Mod), simplePrimBinOp I64),
    -- F64
    ((F64, Add), simplePrimBinOp F64),
    ((F64, Sub), simplePrimBinOp F64),
    ((F64, Mul), simplePrimBinOp F64),
    ((F64, Div), simplePrimBinOp F64)
  ]
