module TypeInference.InferTypes where

import Syntax.ATerms
import Syntax.STerms
import Syntax.Types
import Syntax.TypeGraph
import Utils
import Syntax.Program


import TypeAutomata.ToAutomaton
import TypeAutomata.Determinize
import TypeAutomata.Minimize
import TypeAutomata.FromAutomaton
import TypeAutomata.FlowAnalysis
import TypeInference.GenerateConstraints
import TypeInference.SolveConstraints (solveConstraints)

------------------------------------------------------------------------------
-- TypeInference Trace
------------------------------------------------------------------------------

data TypeInferenceTrace pol = TypeInferenceTrace
  { trace_constraintSet :: ConstraintSet
  , trace_typeAut :: TypeAut
  , trace_typeAutDet :: TypeAutDet
  , trace_typeAutDetAdms :: TypeAutDet
  , trace_minTypeAut :: TypeAutDet
  , trace_resType :: TypeScheme pol
  }

------------------------------------------------------------------------------
-- Symmetric Terms and Commands
------------------------------------------------------------------------------

inferSTermTraced :: PrdCnsRep pc -> STerm pc () -> Environment -> Either Error (TypeInferenceTrace (PrdCnsToPol pc))
inferSTermTraced rep tm env = do
  ((_,ty), constraintSet) <- sgenerateConstraints tm env
  solverState <- solveConstraints constraintSet
  typeAut <- solverStateToTypeAut solverState (prdCnsToPol rep) ty
  let typeAutDet = determinize typeAut
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  let minTypeAut = minimize typeAutDetAdms
  let resType = autToType (prdCnsToPol rep) minTypeAut
  return TypeInferenceTrace
    { trace_constraintSet = constraintSet
    , trace_typeAut = typeAut
    , trace_typeAutDet = typeAutDet
    , trace_typeAutDetAdms = typeAutDetAdms
    , trace_minTypeAut = minTypeAut
    , trace_resType = resType
    }

inferSTermAut :: PrdCnsRep pc -> STerm pc () -> Environment -> Either Error TypeAutDet
inferSTermAut rep tm env = do
  trace <- inferSTermTraced rep tm env
  return $ trace_minTypeAut trace

inferSTerm :: PrdCnsRep pc -> STerm pc () -> Environment -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTerm rep tm env = do
  trace <- inferSTermTraced rep tm env
  return $ trace_resType trace

------------------------------------------------------------------------------
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATermTraced :: ATerm () -> Environment -> Either Error (TypeInferenceTrace Pos)
inferATermTraced tm env = do
  ((_, ty), constraintSet) <- agenerateConstraints tm env
  solverState <- solveConstraints constraintSet
  typeAut <- solverStateToTypeAut solverState PosRep ty
  let typeAutDet = determinize typeAut
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  let minTypeAut = minimize typeAutDetAdms
  let resType = autToType PosRep minTypeAut
  return TypeInferenceTrace
    { trace_constraintSet = constraintSet
    , trace_typeAut = typeAut
    , trace_typeAutDet = typeAutDet
    , trace_typeAutDetAdms = typeAutDetAdms
    , trace_minTypeAut = minTypeAut
    , trace_resType = resType
    }

inferATerm :: ATerm () -> Environment -> Either Error (TypeScheme Pos)
inferATerm tm env = do
  trace <- inferATermTraced tm env
  return $ trace_resType trace

