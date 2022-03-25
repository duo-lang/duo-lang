module Eval.Primitives where

import Syntax.Common
import Syntax.Primitives
import Syntax.AST.Terms

import Eval.Definition
import Errors (throwEvalError)

applyPrdToCns :: Term Prd Compiled -> Term Cns Compiled -> EvalM (Maybe (Command Compiled))
applyPrdToCns x k = pure $ Just $ Apply () (Just $ CBox CBV) x k

evalPrimOp :: PrimitiveType -> PrimitiveOp -> Substitution Compiled -> EvalM (Maybe (Command Compiled))
-- I64
evalPrimOp I64 Add [PrdTerm (PrimLit _ (I64Lit x)), PrdTerm (PrimLit _ (I64Lit y)), CnsTerm k] = applyPrdToCns (PrimLit () (I64Lit (x + y))) k
evalPrimOp I64 Sub [PrdTerm (PrimLit _ (I64Lit x)), PrdTerm (PrimLit _ (I64Lit y)), CnsTerm k] = applyPrdToCns (PrimLit () (I64Lit (x - y))) k
evalPrimOp I64 Mul [PrdTerm (PrimLit _ (I64Lit x)), PrdTerm (PrimLit _ (I64Lit y)), CnsTerm k] = applyPrdToCns (PrimLit () (I64Lit (x * y))) k
evalPrimOp I64 Div [PrdTerm (PrimLit _ (I64Lit x)), PrdTerm (PrimLit _ (I64Lit y)), CnsTerm k] = applyPrdToCns (PrimLit () (I64Lit (x `div` y))) k
evalPrimOp I64 Mod [PrdTerm (PrimLit _ (I64Lit x)), PrdTerm (PrimLit _ (I64Lit y)), CnsTerm k] = applyPrdToCns (PrimLit () (I64Lit (x `mod` y))) k
-- F64
evalPrimOp F64 Add [PrdTerm (PrimLit _ (F64Lit x)), PrdTerm (PrimLit _ (F64Lit y)), CnsTerm k] = applyPrdToCns (PrimLit () (F64Lit (x + y))) k
evalPrimOp F64 Sub [PrdTerm (PrimLit _ (F64Lit x)), PrdTerm (PrimLit _ (F64Lit y)), CnsTerm k] = applyPrdToCns (PrimLit () (F64Lit (x - y))) k
evalPrimOp F64 Mul [PrdTerm (PrimLit _ (F64Lit x)), PrdTerm (PrimLit _ (F64Lit y)), CnsTerm k] = applyPrdToCns (PrimLit () (F64Lit (x * y))) k
evalPrimOp F64 Div [PrdTerm (PrimLit _ (F64Lit x)), PrdTerm (PrimLit _ (F64Lit y)), CnsTerm k] = applyPrdToCns (PrimLit () (F64Lit (x / y))) k
evalPrimOp _   _   _    = throwEvalError ["Undefined primary operation evaluated"]
