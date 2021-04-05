module TypeInference.InferTypes where

import Syntax.ATerms
import Syntax.STerms
import Syntax.Types
import Syntax.TypeAutomaton
import Utils
import Syntax.Program


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

inferSTermTraced :: PrdCnsRep pc -> STerm pc bs -> Environment bs -> Either Error (TypeInferenceTrace (PrdCnsToPol pc))
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

inferSTermAut :: PrdCnsRep pc -> STerm pc bs -> Environment bs -> Either Error (TypeAutDet (PrdCnsToPol pc))
inferSTermAut rep tm env = do
  trace <- inferSTermTraced rep tm env
  return $ trace_minTypeAut trace

inferSTerm :: PrdCnsRep pc -> STerm pc bs -> Environment bs -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTerm rep tm env = do
  trace <- inferSTermTraced rep tm env
  return $ trace_resType trace

checkCmd :: Command bs -> Environment bs -> Either Error ()
checkCmd cmd env = do
  constraints <- snd <$> runGenM env (genConstraintsCommand cmd)
  _ <- solveConstraints constraints
  return ()

------------------------------------------------------------------------------
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATermTraced :: ATerm () bs -> Environment bs -> Either Error (TypeInferenceTrace Pos)
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

inferATerm :: ATerm () bs -> Environment bs -> Either Error (TypeScheme Pos)
inferATerm tm env = do
  trace <- inferATermTraced tm env
  return $ trace_resType trace

