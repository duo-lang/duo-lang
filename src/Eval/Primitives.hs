module Eval.Primitives where

import Syntax.Core.Annot
import Syntax.CST.Kinds
import Syntax.TST.Terms
import Syntax.RST.Terms (PrimitiveOp(..))
import Syntax.CST.Types (PrdCns(..))

import Eval.Definition
import Errors (throwEvalError)
import Utils

applyPrdToCns :: Term Prd -> Term Cns -> EvalM (Maybe Command)
applyPrdToCns x k = pure $ Just $ Apply defaultLoc ApplyAnnotOrig (Just $ CBox CBV) x k

evalPrimOp :: PrimitiveOp -> Substitution -> EvalM (Maybe Command)
-- I64
evalPrimOp I64Add [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 defaultLoc (x + y)) k
evalPrimOp I64Sub [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 defaultLoc (x - y)) k
evalPrimOp I64Mul [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 defaultLoc (x * y)) k
evalPrimOp I64Div [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 defaultLoc (x `div` y)) k
evalPrimOp I64Mod [PrdTerm (PrimLitI64 _ x), PrdTerm (PrimLitI64 _ y), CnsTerm k] = applyPrdToCns (PrimLitI64 defaultLoc (x `mod` y)) k
-- F64
evalPrimOp F64Add [PrdTerm (PrimLitF64 _ x), PrdTerm (PrimLitF64 _ y), CnsTerm k] = applyPrdToCns (PrimLitF64 defaultLoc (x + y)) k
evalPrimOp F64Sub [PrdTerm (PrimLitF64 _ x), PrdTerm (PrimLitF64 _ y), CnsTerm k] = applyPrdToCns (PrimLitF64 defaultLoc (x - y)) k
evalPrimOp F64Mul [PrdTerm (PrimLitF64 _ x), PrdTerm (PrimLitF64 _ y), CnsTerm k] = applyPrdToCns (PrimLitF64 defaultLoc (x * y)) k
evalPrimOp F64Div [PrdTerm (PrimLitF64 _ x), PrdTerm (PrimLitF64 _ y), CnsTerm k] = applyPrdToCns (PrimLitF64 defaultLoc (x / y)) k
-- Char
evalPrimOp CharPrepend [PrdTerm (PrimLitChar _ c), PrdTerm (PrimLitString _ s), CnsTerm k] = applyPrdToCns (PrimLitString defaultLoc (c:s)) k
-- String
evalPrimOp StringAppend [PrdTerm (PrimLitString _ s1), PrdTerm (PrimLitString _ s2), CnsTerm k] = applyPrdToCns (PrimLitString defaultLoc (s1 ++ s2)) k
evalPrimOp _ _  = throwEvalError defaultLoc ["Undefined primary operation evaluated"]
