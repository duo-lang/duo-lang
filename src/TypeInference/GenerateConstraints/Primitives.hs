module TypeInference.GenerateConstraints.Primitives where

import Data.Map

import Syntax.Common.Primitives
    ( PrimitiveOp(..), PrimitiveType(..) )
import Syntax.Common.Polarity
    ( Polarity(Neg), PolarityRep(PosRep, NegRep) )
import Syntax.Common.TypesPol
    ( LinearContext,
      PrdCnsType(PrdCnsType),
      Typ(TyString, TyI64, TyF64, TyChar) )
import Syntax.Common.PrdCns ( PrdCnsRep(CnsRep, PrdRep) )
import Utils ( defaultLoc )

simplePrimBinOp :: PrimitiveType -> LinearContext Neg
simplePrimBinOp I64 = [PrdCnsType PrdRep (TyI64 defaultLoc NegRep), PrdCnsType PrdRep (TyI64 defaultLoc NegRep), PrdCnsType CnsRep (TyI64 defaultLoc PosRep)]
simplePrimBinOp F64 = [PrdCnsType PrdRep (TyF64 defaultLoc NegRep), PrdCnsType PrdRep (TyF64 defaultLoc NegRep), PrdCnsType CnsRep (TyF64 defaultLoc PosRep)]
simplePrimBinOp PChar = [PrdCnsType PrdRep (TyChar defaultLoc NegRep), PrdCnsType PrdRep (TyString defaultLoc NegRep), PrdCnsType CnsRep (TyString defaultLoc PosRep)]
simplePrimBinOp PString = [PrdCnsType PrdRep (TyString defaultLoc NegRep), PrdCnsType PrdRep (TyString defaultLoc NegRep), PrdCnsType CnsRep (TyString defaultLoc PosRep)]

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
    ((F64, Div), simplePrimBinOp F64),
    -- Char
    ((PChar, Prepend), simplePrimBinOp PChar),
    -- String
    ((PString, Append), simplePrimBinOp PString)
  ]
