module TypeInference.InferProgram
  ( TypeInferenceTrace (..)
    -- Symmetric Terms and Commands
  , inferSTermTraced
  , inferSTerm
    -- Asymmetric terms
  , inferATerm
    -- Declarations and Programs
  , insertDecl
  , insertDeclIO
  , inferProgram
  ) where

import Data.Bifunctor (first)
import qualified Data.Map as M

import Pretty.Pretty
import Pretty.Errors
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

generateTypeInferenceTrace :: PolarityRep pol
                           -> ConstraintSet ()
                           -> SolverResult
                           -> Typ pol
                           -> Either Error (TypeInferenceTrace pol)
generateTypeInferenceTrace rep constraintSet solverState typ = do
  typeAut <- solverStateToTypeAut solverState rep typ
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

------------------------------------------------------------------------------
-- Symmetric Terms and Commands
------------------------------------------------------------------------------

inferSTermTraced :: PrdCnsRep pc -> STerm pc Loc bs
                 -> Environment bs
                 -> Either Error (TypeInferenceTrace (PrdCnsToPol pc))
inferSTermTraced rep tm env = do
  ((_,ty), constraintSet) <- runGenM env (genConstraintsSTerm tm)
  solverState <- solveConstraints constraintSet
  generateTypeInferenceTrace (prdCnsToPol rep) constraintSet solverState ty

inferSTermRecTraced :: FreeVarName
                    -> PrdCnsRep pc -> STerm pc Loc bs
                    -> Environment bs
                    -> Either Error (TypeInferenceTrace (PrdCnsToPol pc))
inferSTermRecTraced fv rep tm env = do
  ((_,ty), constraintSet) <- runGenM env (genConstraintsSTermRecursive fv rep tm)
  solverState <- solveConstraints constraintSet
  generateTypeInferenceTrace (prdCnsToPol rep) constraintSet solverState ty


inferSTerm :: PrdCnsRep pc -> STerm pc Loc bs -> Environment bs -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTerm rep tm env = do
  trace <- inferSTermTraced rep tm env
  return $ trace_resType trace

inferSTermRec :: FreeVarName
              -> PrdCnsRep pc -> STerm pc Loc bs
              -> Environment bs
              -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTermRec fv rep tm env = do
  trace <- inferSTermRecTraced fv rep tm env
  return $ trace_resType trace

checkCmd :: Command Loc bs -> Environment bs -> Either Error (ConstraintSet (), SolverResult)
checkCmd cmd env = do
  constraints <- snd <$> runGenM env (genConstraintsCommand cmd)
  solverResult <- solveConstraints constraints
  return (constraints, solverResult)

------------------------------------------------------------------------------
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATermTraced :: ATerm Loc bs -> Environment bs -> Either Error (TypeInferenceTrace Pos)
inferATermTraced tm env = do
  ((_, ty), constraintSet) <- runGenM env (genConstraintsATerm tm)
  solverState <- solveConstraints constraintSet
  generateTypeInferenceTrace PosRep constraintSet solverState ty

inferATermRecTraced :: FreeVarName -> ATerm Loc bs -> Environment bs -> Either Error (TypeInferenceTrace Pos)
inferATermRecTraced v tm env = do
  ((_, ty), constraintSet) <- runGenM env (genConstraintsATermRecursive v tm)
  solverState <- solveConstraints constraintSet
  generateTypeInferenceTrace PosRep constraintSet solverState ty

inferATerm :: ATerm Loc bs -> Environment bs -> Either Error (TypeScheme Pos)
inferATerm tm env = do
  trace <- inferATermTraced tm env
  return $ trace_resType trace

inferATermRec :: FreeVarName -> ATerm Loc bs -> Environment bs -> Either Error (TypeScheme Pos)
inferATermRec v tm env = do
  trace <- inferATermRecTraced v tm env
  return $ trace_resType trace

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
  _ <- first (Located loc) $ checkCmd loct env
  return $ env { cmdEnv  = M.insert v t cmdEnv }
insertDecl (DefDecl loc v t)  env@Environment { defEnv }  = do
  ty <- first (Located loc) $ inferATermRec v t env
  return $ env { defEnv  = M.insert v (first (const ()) t,ty) defEnv }
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

------------------------------------------------------------------------------
-- Verbose type inference of programs
------------------------------------------------------------------------------

insertDeclIO :: Declaration bs -> Environment bs -> IO (Maybe (Environment bs))
insertDeclIO (PrdDecl loc v loct)  env@Environment { prdEnv }  = do
  let t = first (const ()) loct
  case inferSTermRecTraced v PrdRep loct env of
    Left err -> do
      printLocatedError (Located loc err)
      return Nothing
    Right trace -> do
      ppPrintIO (trace_constraintSet trace)
      let newEnv = env { prdEnv  = M.insert v (t,trace_resType trace) prdEnv }
      return (Just newEnv)
insertDeclIO (CnsDecl loc v loct)  env@Environment { cnsEnv }  = do
  let t = first (const ()) loct
  case inferSTermRecTraced v CnsRep loct env of
    Left err -> do
      printLocatedError (Located loc err)
      return Nothing
    Right trace -> do
      ppPrintIO (trace_constraintSet trace)
      let newEnv = env { cnsEnv  = M.insert v (t,trace_resType trace) cnsEnv }
      return (Just newEnv)
insertDeclIO (CmdDecl loc v loct)  env@Environment { cmdEnv }  = do
  let t = first (const ()) loct
  case checkCmd loct env of
    Left err -> do
      printLocatedError (Located loc err)
      return Nothing
    Right (constraints, solverResult) -> do
      ppPrintIO constraints
      ppPrintIO solverResult
      return (Just (env { cmdEnv  = M.insert v t cmdEnv }))
insertDeclIO (DefDecl loc v t)  env@Environment { defEnv }  = do
  case inferATermRecTraced v t env of
    Left err -> do
      printLocatedError (Located loc err)
      return Nothing
    Right trace -> do
      ppPrintIO (trace_constraintSet trace)
      let newEnv = env { defEnv  = M.insert v (first (const ()) t,trace_resType trace) defEnv }
      return (Just newEnv)
insertDeclIO (DataDecl _loc dcl) env@Environment { declEnv } = do
  return (Just (env { declEnv = dcl : declEnv }))
