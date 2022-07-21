module TypeInference.GenerateConstraints.Primitives where

import Data.Map

import Syntax.Common
import Syntax.Common.TypesPol
import Utils

simplePrimBinOp :: PrimitiveType -> LinearContext Neg
simplePrimBinOp I64 = [PrdCnsType PrdRep (TyI64 defaultLoc NegRep), PrdCnsType PrdRep (TyI64 defaultLoc NegRep), PrdCnsType CnsRep (TyI64 defaultLoc PosRep)]
simplePrimBinOp F64 = [PrdCnsType PrdRep (TyF64 defaultLoc NegRep), PrdCnsType PrdRep (TyF64 defaultLoc NegRep), PrdCnsType CnsRep (TyF64 defaultLoc PosRep)]

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
