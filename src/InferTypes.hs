module InferTypes where

import Syntax.Terms
import Syntax.Types
import Syntax.TypeGraph
import Utils
import Syntax.Program
import GenerateConstraints
import SolveConstraints
import TypeAutomata.Determinize
import TypeAutomata.Minimize
import TypeAutomata.FromAutomaton
import TypeAutomata.FlowAnalysis


data TypeInferenceTrace = TypeInferenceTrace
  { trace_constraints :: [Constraint]
  , trace_uvars :: [UVar]
  , trace_typeAut :: TypeAut
  , trace_typeAutDet :: TypeAutDet
  , trace_typeAutDetAdms :: TypeAutDet
  , trace_minTypeAut :: TypeAutDet
  , trace_resType :: TypeScheme
  }

inferPrdTraced :: Term Prd () -> Environment -> Either Error TypeInferenceTrace
inferPrdTraced tm env = do
  (typedTerm, css, uvars) <- generateConstraints tm env
  ty <- typedTermToType env typedTerm
  typeAut <- solveConstraints css uvars ty Prd
  let typeAutDet = determinize typeAut
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  let minTypeAut = minimize typeAutDetAdms
  let resType = autToType minTypeAut
  return TypeInferenceTrace
    { trace_constraints = css
    , trace_uvars = uvars
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
