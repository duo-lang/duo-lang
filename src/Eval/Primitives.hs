module Eval.Primitives where

import Syntax.Common
import Syntax.AST.Terms

import Eval.Definition
import Errors (throwEvalError)

applyPrdToCns :: Term Prd Compiled -> Term Cns Compiled -> EvalM (Maybe (Command Compiled))
applyPrdToCns x k = pure $ Just $ Apply () (Just $ CBox CBV) x k

evalPrimOp :: PrimitiveType -> PrimitiveOp -> Substitution Compiled -> EvalM (Maybe (Command Compiled))
-- I64
evalPrimOp I64 Add [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 () (x + y)) k
evalPrimOp I64 Sub [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 () (x - y)) k
evalPrimOp I64 Mul [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 () (x * y)) k
evalPrimOp I64 Div [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 () (x `div` y)) k
evalPrimOp I64 Mod [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 () (x `mod` y)) k
-- F64
evalPrimOp F64 Add [PrdTerm (PrimLitF64 _ x), PrdTerm (PrimLitF64 _ y), CnsTerm k] = applyPrdToCns (PrimLitF64 () (x + y)) k
evalPrimOp F64 Sub [PrdTerm (PrimLitF64 _ x), PrdTerm (PrimLitF64 _ y), CnsTerm k] = applyPrdToCns (PrimLitF64 () (x - y)) k
evalPrimOp F64 Mul [PrdTerm (PrimLitF64 _ x), PrdTerm (PrimLitF64 _ y), CnsTerm k] = applyPrdToCns (PrimLitF64 () (x * y)) k
evalPrimOp F64 Div [PrdTerm (PrimLitF64 _ x), PrdTerm (PrimLitF64 _ y), CnsTerm k] = applyPrdToCns (PrimLitF64 () (x / y)) k
evalPrimOp _   _   _    = throwEvalError ["Undefined primary operation evaluated"]
