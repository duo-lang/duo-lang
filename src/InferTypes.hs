module InferTypes where

import Syntax.SymmetricTerm
import Syntax.Types
import Syntax.TypeGraph
import Utils
import Syntax.Program
import GenerateConstraints
import SolveConstraints (solveConstraints)
import TypeAutomata.ToAutomaton
import TypeAutomata.Determinize
import TypeAutomata.Minimize
import TypeAutomata.FromAutomaton
import TypeAutomata.FlowAnalysis


data TypeInferenceTrace = TypeInferenceTrace
  { trace_constraintSet :: ConstraintSet
  , trace_typeAut :: TypeAut
  , trace_typeAutDet :: TypeAutDet
  , trace_typeAutDetAdms :: TypeAutDet
  , trace_minTypeAut :: TypeAutDet
  , trace_resType :: TypeScheme
  }

inferPrdTraced :: Term Prd () -> Environment -> Either Error TypeInferenceTrace
inferPrdTraced tm env = do
  (typedTerm, constraintSet) <- generateConstraints tm env
  ty <- typedTermToType env typedTerm
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

inferPrdAut :: Term Prd () -> Environment -> Either Error TypeAutDet
inferPrdAut tm env = do
  trace <- inferPrdTraced tm env
  return $ trace_minTypeAut trace

inferPrd :: Term Prd () -> Environment -> Either Error TypeScheme
inferPrd tm env = do
  trace <- inferPrdTraced tm env
  return $ trace_resType trace
