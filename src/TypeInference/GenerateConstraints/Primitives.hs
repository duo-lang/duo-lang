module TypeInference.GenerateConstraints.Primitives where

import Syntax.Common.Primitives
    ( PrimitiveOp(..), PrimitiveType(..) )
import Syntax.Common.Polarity
    ( Polarity(Neg), PolarityRep(PosRep, NegRep) )
import Syntax.RST.Types
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
primOps :: PrimitiveOp -> LinearContext Neg
-- I64
primOps I64Add = simplePrimBinOp I64
primOps I64Sub = simplePrimBinOp I64
primOps I64Mul = simplePrimBinOp I64
primOps I64Div = simplePrimBinOp I64
primOps I64Mod = simplePrimBinOp I64
-- F64
primOps F64Add = simplePrimBinOp F64
primOps F64Sub = simplePrimBinOp F64
primOps F64Mul = simplePrimBinOp F64
primOps F64Div = simplePrimBinOp F64
-- Char
primOps CharPrepend = simplePrimBinOp PChar
-- String
primOps StringAppend = simplePrimBinOp PString

