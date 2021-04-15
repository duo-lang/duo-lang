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

import Control.Monad (when)
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
  { trace_constraintSet :: ConstraintSet
  , trace_solvedConstraints :: SolverResult
  , trace_typeAut :: TypeAut pol
  , trace_typeAutDet :: TypeAutDet pol
  , trace_typeAutDetAdms :: TypeAutDet pol
  , trace_minTypeAut :: TypeAutDet pol
  , trace_resType :: TypeScheme pol
  }

generateTypeInferenceTrace :: PolarityRep pol
                           -> ConstraintSet
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
    , trace_solvedConstraints = solverState
    , trace_typeAut = typeAut
    , trace_typeAutDet = typeAutDet
    , trace_typeAutDetAdms = typeAutDetAdms
    , trace_minTypeAut = minTypeAut
    , trace_resType = resType
    }

------------------------------------------------------------------------------
-- Symmetric Terms and Commands
------------------------------------------------------------------------------

inferSTermTraced :: IsRec
                 -> FreeVarName
                 -> PrdCnsRep pc -> STerm pc Loc FreeVarName
                 -> Environment FreeVarName
                 -> Either Error (TypeInferenceTrace (PrdCnsToPol pc))
inferSTermTraced isRec fv rep tm env = do
  let genFun = case isRec of
        Recursive -> genConstraintsSTermRecursive fv rep tm
        NonRecursive -> genConstraintsSTerm tm
  ((_,ty), constraintSet) <- runGenM env genFun
  solverState <- solveConstraints constraintSet
  generateTypeInferenceTrace (prdCnsToPol rep) constraintSet solverState ty

inferSTerm :: IsRec
           -> FreeVarName
           -> PrdCnsRep pc -> STerm pc Loc FreeVarName
           -> Environment FreeVarName
           -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTerm isRec fv rep tm env = do
  trace <- inferSTermTraced isRec fv rep tm env
  return $ trace_resType trace

checkCmd :: Command Loc FreeVarName -> Environment FreeVarName -> Either Error (ConstraintSet, SolverResult)
checkCmd cmd env = do
  constraints <- snd <$> runGenM env (genConstraintsCommand cmd)
  solverResult <- solveConstraints constraints
  return (constraints, solverResult)

------------------------------------------------------------------------------
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATermTraced :: IsRec
                 -> FreeVarName
                 -> ATerm Loc FreeVarName
                 -> Environment FreeVarName
                 -> Either Error (TypeInferenceTrace Pos)
inferATermTraced isRec fv tm env = do
  let genFun = case isRec of
        Recursive -> genConstraintsATermRecursive fv tm
        NonRecursive -> genConstraintsATerm tm
  ((_, ty), constraintSet) <- runGenM env genFun
  solverState <- solveConstraints constraintSet
  generateTypeInferenceTrace PosRep constraintSet solverState ty

inferATerm :: IsRec
           -> FreeVarName
           -> ATerm Loc FreeVarName
           -> Environment FreeVarName
           -> Either Error (TypeScheme Pos)
inferATerm isRec fv tm env = do
  trace <- inferATermTraced isRec fv tm env
  return $ trace_resType trace

------------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------------

insertDecl :: Declaration FreeVarName
           -> Environment FreeVarName
           -> Either LocatedError (Environment FreeVarName)
insertDecl (PrdDecl isRec loc v loct)  env@Environment { prdEnv }  = do
  ty <- first (Located loc) (inferSTerm isRec v PrdRep loct env)
  return $ env { prdEnv  = M.insert v (first (const ()) loct, ty) prdEnv }
insertDecl (CnsDecl isRec loc v loct)  env@Environment { cnsEnv }  = do
  ty <- first (Located loc) (inferSTerm isRec v CnsRep loct env)
  return $ env { cnsEnv  = M.insert v (first (const ()) loct, ty) cnsEnv }
insertDecl (CmdDecl loc v loct)  env@Environment { cmdEnv }  = do
  _ <- first (Located loc) $ checkCmd loct env
  return $ env { cmdEnv  = M.insert v (first (const ()) loct) cmdEnv }
insertDecl (DefDecl isRec loc v t)  env@Environment { defEnv }  = do
  ty <- first (Located loc) (inferATerm isRec v t env)
  return $ env { defEnv  = M.insert v (first (const ()) t,ty) defEnv }
insertDecl (DataDecl _loc dcl) env@Environment { declEnv } = do
  return $ env { declEnv = dcl : declEnv }

inferProgram :: [Declaration FreeVarName] -> Either LocatedError (Environment FreeVarName)
inferProgram = inferProgram' mempty
  where
    inferProgram' :: Environment FreeVarName
                  -> [Declaration FreeVarName]
                  -> Either LocatedError (Environment FreeVarName)
    inferProgram' env [] = return env
    inferProgram' env (decl:decls) = do
      env' <- insertDecl decl env
      inferProgram' env' decls

------------------------------------------------------------------------------
-- Verbose type inference of programs
------------------------------------------------------------------------------

insertDeclIO :: Verbosity
             -> Declaration FreeVarName
             -> Environment FreeVarName
             -> IO (Maybe (Environment FreeVarName))
insertDeclIO verb (PrdDecl isRec loc v loct)  env@Environment { prdEnv }  = do
  case inferSTermTraced isRec v PrdRep loct env of
    Left err -> do
      printLocatedError (Located loc err)
      return Nothing
    Right trace -> do
      when (verb == Verbose) $ do
        ppPrintIO (trace_constraintSet trace)
        ppPrintIO (trace_solvedConstraints trace)
      let newEnv = env { prdEnv  = M.insert v ( first (const ()) loct ,trace_resType trace) prdEnv }
      putStr "Inferred type: "
      ppPrintIO (trace_resType trace)
      return (Just newEnv)
insertDeclIO verb (CnsDecl isRec loc v loct)  env@Environment { cnsEnv }  = do
  case inferSTermTraced isRec v CnsRep loct env of
    Left err -> do
      printLocatedError (Located loc err)
      return Nothing
    Right trace -> do
      when (verb == Verbose) $ do
        ppPrintIO (trace_constraintSet trace)
        ppPrintIO (trace_solvedConstraints trace)
      let newEnv = env { cnsEnv  = M.insert v (first (const ()) loct,trace_resType trace) cnsEnv }
      putStr "Inferred type: "
      ppPrintIO (trace_resType trace)
      return (Just newEnv)
insertDeclIO verb (CmdDecl loc v loct)  env@Environment { cmdEnv }  = do
  case checkCmd loct env of
    Left err -> do
      printLocatedError (Located loc err)
      return Nothing
    Right (constraints, solverResult) -> do
      when (verb == Verbose) $ do
        ppPrintIO constraints
        ppPrintIO solverResult
      return (Just (env { cmdEnv  = M.insert v (first (const ()) loct) cmdEnv }))
insertDeclIO verb (DefDecl isRec loc v t)  env@Environment { defEnv }  = do
  case inferATermTraced isRec v t env of
    Left err -> do
      printLocatedError (Located loc err)
      return Nothing
    Right trace -> do
      when (verb == Verbose) $ do
        ppPrintIO (trace_constraintSet trace)
        ppPrintIO (trace_solvedConstraints trace)
      let newEnv = env { defEnv  = M.insert v (first (const ()) t,trace_resType trace) defEnv }
      putStr "Inferred type: "
      ppPrintIO (trace_resType trace)
      return (Just newEnv)
insertDeclIO _ (DataDecl _loc dcl) env@Environment { declEnv } = do
  return (Just (env { declEnv = dcl : declEnv }))
