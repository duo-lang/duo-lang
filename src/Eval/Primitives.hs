module Eval.Primitives where

import Syntax.Core.Annot
import Syntax.CST.Kinds
import Syntax.TST.Terms
import Syntax.RST.Terms (PrimitiveOp(..))
import Syntax.CST.Types (PrdCns(..))

import Eval.Definition
import Errors (throwEvalError)
import Loc

applyPrdToCns :: Term Prd -> Term Cns -> EvalM (Maybe Command)
applyPrdToCns x k = pure $ Just $ Apply defaultLoc ApplyAnnotOrig (CBox CBV) x k

evalPrimOp :: PrimitiveOp -> Substitution -> EvalM (Maybe Command)
-- I64
evalPrimOp I64Add       (MkSubstitution [PrdTerm (PrimLitI64 _ x),      PrdTerm (PrimLitI64 _ y), CnsTerm k]) = applyPrdToCns (PrimLitI64 defaultLoc (x + y)) k
evalPrimOp I64Sub       (MkSubstitution [PrdTerm (PrimLitI64 _ x),      PrdTerm (PrimLitI64 _ y), CnsTerm k]) = applyPrdToCns (PrimLitI64 defaultLoc (x - y)) k
evalPrimOp I64Mul       (MkSubstitution [PrdTerm (PrimLitI64 _ x),      PrdTerm (PrimLitI64 _ y), CnsTerm k]) = applyPrdToCns (PrimLitI64 defaultLoc (x * y)) k
evalPrimOp I64Div       (MkSubstitution [PrdTerm (PrimLitI64 _ x),      PrdTerm (PrimLitI64 _ y), CnsTerm k]) = applyPrdToCns (PrimLitI64 defaultLoc (x `div` y)) k
evalPrimOp I64Mod       (MkSubstitution [PrdTerm (PrimLitI64 _ x),      PrdTerm (PrimLitI64 _ y), CnsTerm k]) = applyPrdToCns (PrimLitI64 defaultLoc (x `mod` y)) k
-- F64
evalPrimOp F64Add       (MkSubstitution [PrdTerm (PrimLitF64 _ x),      PrdTerm (PrimLitF64 _ y), CnsTerm k]) = applyPrdToCns (PrimLitF64 defaultLoc (x + y)) k
evalPrimOp F64Sub       (MkSubstitution [PrdTerm (PrimLitF64 _ x),      PrdTerm (PrimLitF64 _ y), CnsTerm k]) = applyPrdToCns (PrimLitF64 defaultLoc (x - y)) k
evalPrimOp F64Mul       (MkSubstitution [PrdTerm (PrimLitF64 _ x),      PrdTerm (PrimLitF64 _ y), CnsTerm k]) = applyPrdToCns (PrimLitF64 defaultLoc (x * y)) k
evalPrimOp F64Div       (MkSubstitution [PrdTerm (PrimLitF64 _ x),      PrdTerm (PrimLitF64 _ y), CnsTerm k]) = applyPrdToCns (PrimLitF64 defaultLoc (x / y)) k
-- Char
evalPrimOp CharPrepend  (MkSubstitution [PrdTerm (PrimLitChar _ c),     PrdTerm (PrimLitString _ s), CnsTerm k]) = applyPrdToCns (PrimLitString defaultLoc (c:s)) k
-- String
evalPrimOp StringAppend (MkSubstitution [PrdTerm (PrimLitString _ s1),  PrdTerm (PrimLitString _ s2), CnsTerm k]) = applyPrdToCns (PrimLitString defaultLoc (s1 ++ s2)) k
evalPrimOp _ _  = throwEvalError defaultLoc ["Undefined primary operation evaluated"]
