module TypeInference.InferProgram ( insertDecl, inferProgram )where

import Data.Bifunctor (first)
import qualified Data.Map as M

import Syntax.ATerms
import Syntax.STerms
import Syntax.Types
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
-- Symmetric Terms and Commands
------------------------------------------------------------------------------

inferSTerm :: FreeVarName -> PrdCnsRep pc -> STerm pc () bs -> Environment bs -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTerm fv rep tm env = do
  ((_,ty), constraintSet) <- runGenM env (genConstraintsSTermRecursive fv rep tm)
  solverState <- solveConstraints constraintSet
  typeAut <- solverStateToTypeAut solverState (prdCnsToPol rep) ty
  let typeAutDet = determinize typeAut
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  let minTypeAut = minimize typeAutDetAdms
  let resType = autToType minTypeAut
  return resType

checkCmd :: Command () bs -> Environment bs -> Either Error ()
checkCmd cmd env = do
  constraints <- snd <$> runGenM env (genConstraintsCommand cmd)
  _ <- solveConstraints constraints
  return ()

------------------------------------------------------------------------------
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATerm :: FreeVarName -> ATerm ext bs -> Environment bs -> Either Error (ATerm () bs, TypeScheme Pos)
inferATerm v tm env = do
  ((tm, ty), constraintSet) <- runGenM env (genConstraintsATermRecursive v tm)
  solverState <- solveConstraints constraintSet
  typeAut <- solverStateToTypeAut solverState PosRep ty
  let typeAutDet = determinize typeAut
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  let minTypeAut = minimize typeAutDetAdms
  let resType = autToType minTypeAut
  return (tm, resType)

insertDecl :: Declaration bs -> Environment bs -> Either LocatedError (Environment bs)
insertDecl (PrdDecl loc v loct)  env@Environment { prdEnv }  = do
  let t = first (const ()) loct
  ty <- first (Located loc) $ inferSTerm v PrdRep t env
  return $ env { prdEnv  = M.insert v (t,ty) prdEnv }
insertDecl (CnsDecl loc v loct)  env@Environment { cnsEnv }  = do
  let t = first (const ()) loct
  ty <- first (Located loc) $ inferSTerm v CnsRep t env
  return $ env { cnsEnv  = M.insert v (t,ty) cnsEnv }
insertDecl (CmdDecl loc v loct)  env@Environment { cmdEnv }  = do
  let t = first (const ()) loct
  first (Located loc) $ checkCmd t env
  return $ env { cmdEnv  = M.insert v t cmdEnv }
insertDecl (DefDecl loc v t)  env@Environment { defEnv }  = do
  (tm,ty) <- first (Located loc) $ inferATerm v t env
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
