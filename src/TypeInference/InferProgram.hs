module TypeInference.InferProgram
  ( TypeInferenceTrace (..)
    -- Symmetric Terms and Commands
  , inferSTermTraced
  , inferSTerm
    -- Asymmetric terms
  , inferATerm
    -- Declarations and Programs
  , insertDecl
  , inferProgram
  ) where

import Data.Bifunctor (first)
import qualified Data.Map as M

import Syntax.ATerms
import Syntax.STerms
import Syntax.Types
import Syntax.TypeAutomaton
import Syntax.Program
import Utils

import TypeAutomata.ToAutomaton
import TypeAutomata.Determinize
import TypeAutomata.Minimize
import TypeAutomata.FromAutomaton
import TypeAutomata.FlowAnalysis
import TypeInference.GenerateConstraints.Definition
import TypeInference.GenerateConstraints.ATerms
import TypeInference.GenerateConstraints.STerms
import TypeInference.SolveConstraints (solveConstraints)

------------------------------------------------------------------------------
-- TypeInference Trace
------------------------------------------------------------------------------

data TypeInferenceTrace pol = TypeInferenceTrace
  { trace_constraintSet :: ConstraintSet ()
  , trace_typeAut :: TypeAut pol
  , trace_typeAutDet :: TypeAutDet pol
  , trace_typeAutDetAdms :: TypeAutDet pol
  , trace_minTypeAut :: TypeAutDet pol
  , trace_resType :: TypeScheme pol
  }

------------------------------------------------------------------------------
-- Symmetric Terms and Commands
------------------------------------------------------------------------------

inferSTermTraced :: PrdCnsRep pc -> STerm pc Loc bs -> Environment bs -> Either Error (TypeInferenceTrace (PrdCnsToPol pc))
inferSTermTraced rep tm env = do
  ((_,ty), constraintSet) <- runGenM env (genConstraintsSTerm tm)
  solverState <- solveConstraints constraintSet
  typeAut <- solverStateToTypeAut solverState (prdCnsToPol rep) ty
  let typeAutDet = determinize typeAut
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  let minTypeAut = minimize typeAutDetAdms
  let resType = autToType minTypeAut
  return TypeInferenceTrace
    { trace_constraintSet = constraintSet
    , trace_typeAut = typeAut
    , trace_typeAutDet = typeAutDet
    , trace_typeAutDetAdms = typeAutDetAdms
    , trace_minTypeAut = minTypeAut
    , trace_resType = resType
    }

inferSTerm :: PrdCnsRep pc -> STerm pc Loc bs -> Environment bs -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTerm rep tm env = do
  trace <- inferSTermTraced rep tm env
  return $ trace_resType trace

inferSTermRec :: FreeVarName -> PrdCnsRep pc -> STerm pc Loc bs -> Environment bs -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTermRec fv rep tm env = do
  ((_,ty), constraintSet) <- runGenM env (genConstraintsSTermRecursive fv rep tm)
  solverState <- solveConstraints constraintSet
  typeAut <- solverStateToTypeAut solverState (prdCnsToPol rep) ty
  let typeAutDet = determinize typeAut
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  let minTypeAut = minimize typeAutDetAdms
  let resType = autToType minTypeAut
  return resType

checkCmd :: Command Loc bs -> Environment bs -> Either Error ()
checkCmd cmd env = do
  constraints <- snd <$> runGenM env (genConstraintsCommand cmd)
  _ <- solveConstraints constraints
  return ()

------------------------------------------------------------------------------
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATermTraced :: ATerm Loc bs -> Environment bs -> Either Error (TypeInferenceTrace Pos)
inferATermTraced tm env = do
  ((_, ty), constraintSet) <- runGenM env (genConstraintsATerm tm)
  solverState <- solveConstraints constraintSet
  typeAut <- solverStateToTypeAut solverState PosRep ty
  let typeAutDet = determinize typeAut
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  let minTypeAut = minimize typeAutDetAdms
  let resType = autToType minTypeAut
  return TypeInferenceTrace
    { trace_constraintSet = constraintSet
    , trace_typeAut = typeAut
    , trace_typeAutDet = typeAutDet
    , trace_typeAutDetAdms = typeAutDetAdms
    , trace_minTypeAut = minTypeAut
    , trace_resType = resType
    }

inferATerm :: ATerm Loc bs -> Environment bs -> Either Error (TypeScheme Pos)
inferATerm tm env = do
  trace <- inferATermTraced tm env
  return $ trace_resType trace

inferATermRec :: FreeVarName -> ATerm Loc bs -> Environment bs -> Either Error (ATerm () bs, TypeScheme Pos)
inferATermRec v tm env = do
  ((tm, ty), constraintSet) <- runGenM env (genConstraintsATermRecursive v tm)
  solverState <- solveConstraints constraintSet
  typeAut <- solverStateToTypeAut solverState PosRep ty
  let typeAutDet = determinize typeAut
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  let minTypeAut = minimize typeAutDetAdms
  let resType = autToType minTypeAut
  return (tm, resType)

------------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------------

insertDecl :: Declaration bs -> Environment bs -> Either LocatedError (Environment bs)
insertDecl (PrdDecl loc v loct)  env@Environment { prdEnv }  = do
  let t = first (const ()) loct
  ty <- first (Located loc) $ inferSTermRec v PrdRep loct env
  return $ env { prdEnv  = M.insert v (t,ty) prdEnv }
insertDecl (CnsDecl loc v loct)  env@Environment { cnsEnv }  = do
  let t = first (const ()) loct
  ty <- first (Located loc) $ inferSTermRec v CnsRep loct env
  return $ env { cnsEnv  = M.insert v (t,ty) cnsEnv }
insertDecl (CmdDecl loc v loct)  env@Environment { cmdEnv }  = do
  let t = first (const ()) loct
  first (Located loc) $ checkCmd loct env
  return $ env { cmdEnv  = M.insert v t cmdEnv }
insertDecl (DefDecl loc v t)  env@Environment { defEnv }  = do
  (tm,ty) <- first (Located loc) $ inferATermRec v t env
  return $ env { defEnv  = M.insert v (tm,ty) defEnv }
insertDecl (DataDecl _loc dcl) env@Environment { declEnv } = do
  return $ env { declEnv = dcl : declEnv }

inferProgram :: [Declaration bs] -> Either LocatedError (Environment bs)
inferProgram = inferProgram' mempty
  where
    inferProgram' :: Environment bs -> [Declaration bs] -> Either LocatedError (Environment bs)
    inferProgram' env [] = return env
    inferProgram' env (decl:decls) = do
      env' <- insertDecl decl env
      inferProgram' env' decls
