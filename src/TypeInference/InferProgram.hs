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
import TypeAutomata.Definition
import Syntax.Program
import Utils

import TypeAutomata.ToAutomaton
import TypeAutomata.Determinize
import TypeAutomata.Minimize
import TypeAutomata.FromAutomaton
import TypeAutomata.RemoveAdmissible
import TypeAutomata.Subsume (subsume)
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
                 -> InferenceMode
                 -> PrdCnsRep pc -> STerm pc Loc FreeVarName
                 -> Environment FreeVarName
                 -> Either Error (TypeInferenceTrace (PrdCnsToPol pc))
inferSTermTraced isRec fv im rep tm env = do
  let genFun = case isRec of
        Recursive -> genConstraintsSTermRecursive fv im rep tm
        NonRecursive -> genConstraintsSTerm im tm
  ((_,ty), constraintSet) <- runGenM env genFun
  solverState <- solveConstraints constraintSet env
  generateTypeInferenceTrace (prdCnsToPol rep) constraintSet solverState ty

inferSTerm :: IsRec
           -> FreeVarName
           -> InferenceMode
           -> PrdCnsRep pc -> STerm pc Loc FreeVarName
           -> Environment FreeVarName
           -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTerm isRec fv im rep tm env = do
  trace <- inferSTermTraced isRec fv im rep tm env
  return $ trace_resType trace

checkCmd :: Command Loc FreeVarName
         -> Environment FreeVarName
         -> InferenceMode
         -> Either Error (ConstraintSet, SolverResult)
checkCmd cmd env im = do
  constraints <- snd <$> runGenM env (genConstraintsCommand im cmd)
  solverResult <- solveConstraints constraints env
  return (constraints, solverResult)

------------------------------------------------------------------------------
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATermTraced :: IsRec
                 -> FreeVarName
                 -> InferenceMode
                 -> ATerm Loc FreeVarName
                 -> Environment FreeVarName
                 -> Either Error (TypeInferenceTrace Pos)
inferATermTraced isRec fv im tm env = do
  let genFun = case isRec of
        Recursive -> genConstraintsATermRecursive im fv tm
        NonRecursive -> genConstraintsATerm im tm
  ((_, ty), constraintSet) <- runGenM env genFun
  solverState <- solveConstraints constraintSet env
  generateTypeInferenceTrace PosRep constraintSet solverState ty

inferATerm :: IsRec
           -> FreeVarName
           -> InferenceMode
           -> ATerm Loc FreeVarName
           -> Environment FreeVarName
           -> Either Error (TypeScheme Pos)
inferATerm isRec fv im tm env = do
  trace <- inferATermTraced isRec fv im tm env
  return $ trace_resType trace

------------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------------

checkAnnot :: TypeScheme pol -> (Maybe (TypeScheme pol)) -> Either Error (TypeScheme pol)
checkAnnot ty Nothing = return ty
checkAnnot ty (Just tyAnnot) = do
  isSubsumed <- subsume ty tyAnnot
  case isSubsumed of
    True -> return tyAnnot
    False -> Left (OtherError (unlines [ "Annotated type is not subsumed by inferred type"
                                       , " Annotated type: " <> ppPrint tyAnnot
                                       , " Inferred type:  " <> ppPrint ty]))

insertDecl :: Declaration FreeVarName
           -> Environment FreeVarName
           -> InferenceMode
           -> Either LocatedError (Environment FreeVarName)
insertDecl (PrdDecl isRec loc v annot loct)  env@Environment { prdEnv } im = do
  ty <- first (Located loc) (inferSTerm isRec v im PrdRep loct env)
  ty <- first (Located loc) (checkAnnot ty annot)
  return $ env { prdEnv  = M.insert v (first (const ()) loct, ty) prdEnv }
insertDecl (CnsDecl isRec loc v annot loct)  env@Environment { cnsEnv } im = do
  ty <- first (Located loc) (inferSTerm isRec v im CnsRep loct env)
  ty <- first (Located loc) (checkAnnot ty annot)
  return $ env { cnsEnv  = M.insert v (first (const ()) loct, ty) cnsEnv }
insertDecl (CmdDecl loc v loct)  env@Environment { cmdEnv } im = do
  _ <- first (Located loc) $ checkCmd loct env im
  return $ env { cmdEnv  = M.insert v (first (const ()) loct) cmdEnv }
insertDecl (DefDecl isRec loc v annot t)  env@Environment { defEnv } im = do
  ty <- first (Located loc) (inferATerm isRec v im t env)
  ty <- first (Located loc) (checkAnnot ty annot)
  return $ env { defEnv  = M.insert v (first (const ()) t,ty) defEnv }
insertDecl (DataDecl _loc dcl) env@Environment { declEnv } _ = do
  return $ env { declEnv = dcl : declEnv }

inferProgram :: [Declaration FreeVarName] -> InferenceMode -> Either LocatedError (Environment FreeVarName)
inferProgram  = inferProgram' mempty
  where
    inferProgram' :: Environment FreeVarName
                  -> [Declaration FreeVarName]
                  -> InferenceMode
                  -> Either LocatedError (Environment FreeVarName)
    inferProgram' env [] _ = return env
    inferProgram' env (decl:decls) im = do
      env' <- insertDecl decl env im
      inferProgram' env' decls im

------------------------------------------------------------------------------
-- Verbose type inference of programs
------------------------------------------------------------------------------

insertDeclIO :: Verbosity -> InferenceMode
             -> Declaration FreeVarName
             -> Environment FreeVarName
             -> IO (Maybe (Environment FreeVarName))
insertDeclIO verb im (PrdDecl isRec loc v annot loct)  env@Environment { prdEnv }  = do
  case inferSTermTraced isRec v im PrdRep loct env of
    Left err -> do
      printLocatedError (Located loc err)
      return Nothing
    Right trace -> do
      when (verb == Verbose) $ do
        ppPrintIO (trace_constraintSet trace)
        ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation
      let ty = trace_resType trace
      case checkAnnot ty annot of
        Left err -> ppPrintIO err >> return Nothing
        Right ty -> do
          let newEnv = env { prdEnv  = M.insert v ( first (const ()) loct ,ty) prdEnv }
          putStr "Inferred type: "
          ppPrintIO (trace_resType trace)
          return (Just newEnv)
insertDeclIO verb im (CnsDecl isRec loc v annot loct)  env@Environment { cnsEnv }  = do
  case inferSTermTraced isRec v im CnsRep loct env of
    Left err -> do
      printLocatedError (Located loc err)
      return Nothing
    Right trace -> do
      when (verb == Verbose) $ do
        ppPrintIO (trace_constraintSet trace)
        ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation:
      let ty = trace_resType trace
      case checkAnnot ty annot of
        Left err -> ppPrintIO err >> return Nothing
        Right ty -> do
          let newEnv = env { cnsEnv  = M.insert v (first (const ()) loct,ty) cnsEnv }
          putStr "Inferred type: "
          ppPrintIO (trace_resType trace)
          return (Just newEnv)
insertDeclIO verb im (CmdDecl loc v loct)  env@Environment { cmdEnv }  = do
  case checkCmd loct env im of
    Left err -> do
      printLocatedError (Located loc err)
      return Nothing
    Right (constraints, solverResult) -> do
      when (verb == Verbose) $ do
        ppPrintIO constraints
        ppPrintIO solverResult
      return (Just (env { cmdEnv  = M.insert v (first (const ()) loct) cmdEnv }))
insertDeclIO verb im (DefDecl isRec loc v annot t)  env@Environment { defEnv }  = do
  case inferATermTraced isRec v im t env of
    Left err -> do
      printLocatedError (Located loc err)
      return Nothing
    Right trace -> do
      when (verb == Verbose) $ do
        ppPrintIO (trace_constraintSet trace)
        ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation
      let ty = trace_resType trace
      case checkAnnot ty annot of
        Left err -> ppPrintIO err >> return Nothing
        Right ty -> do
          let newEnv = env { defEnv  = M.insert v (first (const ()) t, ty) defEnv }
          putStr "Inferred type: "
          ppPrintIO (trace_resType trace)
          return (Just newEnv)
insertDeclIO _ _ (DataDecl _loc dcl) env@Environment { declEnv } = do
  return (Just (env { declEnv = dcl : declEnv }))
