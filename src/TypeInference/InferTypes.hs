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

data TypeInferenceTrace = TypeInferenceTrace
  { trace_constraintSet :: ConstraintSet
  , trace_typeAut :: TypeAut
  , trace_typeAutDet :: TypeAutDet
  , trace_typeAutDetAdms :: TypeAutDet
  , trace_minTypeAut :: TypeAutDet
  , trace_resType :: TypeScheme Pos
  }

------------------------------------------------------------------------------
-- Symmetric Terms and Commands
------------------------------------------------------------------------------

inferPrdTraced :: STerm Prd () -> Environment -> Either Error TypeInferenceTrace
inferPrdTraced tm env = do
  ((_,ty), constraintSet) <- sgenerateConstraints tm env
  solverState <- solveConstraints constraintSet
  typeAut <- solverStateToTypeAut solverState ty Prd
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

inferPrdAut :: STerm Prd () -> Environment -> Either Error TypeAutDet
inferPrdAut tm env = do
  trace <- inferPrdTraced tm env
  return $ trace_minTypeAut trace

inferPrd :: STerm Prd () -> Environment -> Either Error (TypeScheme Pos)
inferPrd tm env = do
  trace <- inferPrdTraced tm env
  return $ trace_resType trace

------------------------------------------------------------------------------
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATermTraced :: ATerm () -> Environment -> Either Error TypeInferenceTrace
inferATermTraced tm env = do
  ((_, ty), constraintSet) <- agenerateConstraints tm env
  solverState <- solveConstraints constraintSet
  typeAut <- solverStateToTypeAut solverState ty Prd
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

inferATerm :: ATerm () -> Environment -> Either Error (TypeScheme Pos)
inferATerm tm env = do
  trace <- inferATermTraced tm env
  return $ trace_resType trace

