module TypeInference.GenerateConstraints.Primitives where

import Syntax.Common.Primitives
    ( PrimitiveOp(..) )
import Syntax.Common.Polarity
    ( Polarity(Neg), PolarityRep(PosRep, NegRep) )
import Syntax.RST.Types
    ( LinearContext,
      PrdCnsType(PrdCnsType),
      Typ(TyString, TyI64, TyF64, TyChar) )
import Syntax.Common.PrdCns ( PrdCnsRep(CnsRep, PrdRep) )
import Utils ( defaultLoc )


i64PrimBinOp :: LinearContext Neg
i64PrimBinOp = [PrdCnsType PrdRep (TyI64 defaultLoc NegRep), PrdCnsType PrdRep (TyI64 defaultLoc NegRep), PrdCnsType CnsRep (TyI64 defaultLoc PosRep)]

f64PrimBinOp :: LinearContext Neg
f64PrimBinOp = [PrdCnsType PrdRep (TyF64 defaultLoc NegRep), PrdCnsType PrdRep (TyF64 defaultLoc NegRep), PrdCnsType CnsRep (TyF64 defaultLoc PosRep)]

stringPrimBinOp :: LinearContext Neg
stringPrimBinOp = [PrdCnsType PrdRep (TyString defaultLoc NegRep), PrdCnsType PrdRep (TyString defaultLoc NegRep), PrdCnsType CnsRep (TyString defaultLoc PosRep)]

charPrimBinOp :: LinearContext Neg
charPrimBinOp = [PrdCnsType PrdRep (TyChar defaultLoc NegRep), PrdCnsType PrdRep (TyString defaultLoc NegRep), PrdCnsType CnsRep (TyString defaultLoc PosRep)]

-- | Primitive operations and their signatures
primOps :: PrimitiveOp -> LinearContext Neg
-- I64
primOps I64Add = i64PrimBinOp
primOps I64Sub = i64PrimBinOp
primOps I64Mul = i64PrimBinOp
primOps I64Div = i64PrimBinOp
primOps I64Mod = i64PrimBinOp
-- F64
primOps F64Add = f64PrimBinOp
primOps F64Sub = f64PrimBinOp
primOps F64Mul = f64PrimBinOp
primOps F64Div = f64PrimBinOp
-- Char
primOps CharPrepend = charPrimBinOp
-- String
primOps StringAppend = stringPrimBinOp

