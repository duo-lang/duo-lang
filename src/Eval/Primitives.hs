module Eval.Primitives where

import Syntax.Common
import Syntax.AST.Terms

import Eval.Definition
import Errors (throwEvalError)
import Utils

applyPrdToCns :: Term Prd -> Term Cns -> EvalM (Maybe Command)
applyPrdToCns x k = pure $ Just $ Apply defaultLoc (Just $ CBox CBV) x k

evalPrimOp :: PrimitiveType -> PrimitiveOp -> Substitution -> EvalM (Maybe Command)
-- I64
evalPrimOp I64 Add [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 defaultLoc (x + y)) k
evalPrimOp I64 Sub [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 defaultLoc (x - y)) k
evalPrimOp I64 Mul [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 defaultLoc (x * y)) k
evalPrimOp I64 Div [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 defaultLoc (x `div` y)) k
evalPrimOp I64 Mod [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 defaultLoc (x `mod` y)) k
-- F64
evalPrimOp F64 Add [PrdTerm (PrimLitF64 _ x), PrdTerm (PrimLitF64 _ y), CnsTerm k] = applyPrdToCns (PrimLitF64 defaultLoc (x + y)) k
evalPrimOp F64 Sub [PrdTerm (PrimLitF64 _ x), PrdTerm (PrimLitF64 _ y), CnsTerm k] = applyPrdToCns (PrimLitF64 defaultLoc (x - y)) k
evalPrimOp F64 Mul [PrdTerm (PrimLitF64 _ x), PrdTerm (PrimLitF64 _ y), CnsTerm k] = applyPrdToCns (PrimLitF64 defaultLoc (x * y)) k
evalPrimOp F64 Div [PrdTerm (PrimLitF64 _ x), PrdTerm (PrimLitF64 _ y), CnsTerm k] = applyPrdToCns (PrimLitF64 defaultLoc (x / y)) k
evalPrimOp _   _   _    = throwEvalError ["Undefined primary operation evaluated"]
