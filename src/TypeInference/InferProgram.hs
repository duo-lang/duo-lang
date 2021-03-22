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

inferSTerm :: PrdCnsRep pc -> STerm pc () -> Environment -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTerm rep tm env = do
  ((_,ty), constraintSet) <- runGenM env (genConstraintsSTerm tm)
  solverState <- solveConstraints constraintSet
  typeAut <- solverStateToTypeAut solverState (prdCnsToPol rep) ty
  let typeAutDet = determinize typeAut
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  let minTypeAut = minimize typeAutDetAdms
  let resType = autToType minTypeAut
  return resType

checkCmd :: Command () -> Environment -> Either Error ()
checkCmd cmd env = do
  constraints <- snd <$> runGenM env (genConstraintsCommand cmd)
  _ <- solveConstraints constraints
  return ()

------------------------------------------------------------------------------
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATerm :: ATerm () -> Environment -> Either Error (TypeScheme Pos)
inferATerm tm env = do
  ((_, ty), constraintSet) <- runGenM env (genConstraintsATerm tm)
  solverState <- solveConstraints constraintSet
  typeAut <- solverStateToTypeAut solverState PosRep ty
  let typeAutDet = determinize typeAut
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  let minTypeAut = minimize typeAutDetAdms
  let resType = autToType minTypeAut
  return resType

insertDecl :: Declaration () -> Environment -> Either LocatedError Environment
insertDecl (PrdDecl loc v t)  env@Environment { prdEnv }  = do
  ty <- first (Located loc) $ inferSTerm PrdRep t env
  return $ env { prdEnv  = M.insert v (t,ty) prdEnv }
insertDecl (CnsDecl loc v t)  env@Environment { cnsEnv }  = do
  ty <- first (Located loc) $ inferSTerm CnsRep t env
  return $ env { cnsEnv  = M.insert v (t,ty) cnsEnv }
insertDecl (CmdDecl loc v t)  env@Environment { cmdEnv }  = do
  first (Located loc) $ checkCmd t env
  return $ env { cmdEnv  = M.insert v t cmdEnv }
insertDecl (DefDecl loc v t)  env@Environment { defEnv }  = do
  ty <- first (Located loc) $ inferATerm t env
  return $ env { defEnv  = M.insert v (t,ty) defEnv }
insertDecl (DataDecl _loc dcl) env@Environment { declEnv } = do
  return $ env { declEnv = dcl : declEnv }

inferProgram :: [Declaration ()] -> Either LocatedError Environment
inferProgram = inferProgram' mempty
  where
    inferProgram' :: Environment -> [Declaration ()] -> Either LocatedError Environment
    inferProgram' env [] = return env
    inferProgram' env (decl:decls) = do
      env' <- insertDecl decl env
      inferProgram' env' decls
