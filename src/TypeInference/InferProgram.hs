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
import qualified Data.Text as T

import Errors
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
import TypeAutomata.Lint (lint)
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
  lint typeAut
  let typeAutDet = determinize typeAut
  lint typeAutDet
  let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
  lint typeAutDetAdms
  let minTypeAut = minimize typeAutDetAdms
  lint minTypeAut
  resType <- autToType minTypeAut
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
                 -> Loc
                 -> FreeVarName
                 -> InferenceMode
                 -> PrdCnsRep pc -> STerm pc Loc FreeVarName
                 -> Environment FreeVarName
                 -> Either Error (TypeInferenceTrace (PrdCnsToPol pc))
inferSTermTraced isRec loc fv im rep tm env = do
  let genFun = case isRec of
        Recursive -> genConstraintsSTermRecursive loc fv rep tm
        NonRecursive -> genConstraintsSTerm tm
  ((_,ty), constraintSet) <- runGenM env im genFun
  solverState <- solveConstraints constraintSet env im
  generateTypeInferenceTrace (prdCnsToPol rep) constraintSet solverState ty

inferSTerm :: IsRec
           -> Loc
           -> FreeVarName
           -> InferenceMode
           -> PrdCnsRep pc -> STerm pc Loc FreeVarName
           -> Environment FreeVarName
           -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTerm isRec loc fv im rep tm env = do
  trace <- inferSTermTraced isRec loc fv im rep tm env
  return $ trace_resType trace

checkCmd :: Command Loc FreeVarName
         -> Environment FreeVarName
         -> InferenceMode
         -> Either Error (ConstraintSet, SolverResult)
checkCmd cmd env im = do
  constraints <- snd <$> runGenM env im (genConstraintsCommand cmd)
  solverResult <- solveConstraints constraints env im
  return (constraints, solverResult)

------------------------------------------------------------------------------
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATermTraced :: IsRec
                 -> Loc
                 -> FreeVarName
                 -> InferenceMode
                 -> ATerm Loc FreeVarName
                 -> Environment FreeVarName
                 -> Either Error (TypeInferenceTrace Pos)
inferATermTraced isRec loc fv im tm env = do
  let genFun = case isRec of
        Recursive -> genConstraintsATermRecursive loc fv tm
        NonRecursive -> genConstraintsATerm tm
  ((_, ty), constraintSet) <- runGenM env im genFun
  solverState <- solveConstraints constraintSet env im
  generateTypeInferenceTrace PosRep constraintSet solverState ty

inferATerm :: IsRec
           -> Loc
           -> FreeVarName
           -> InferenceMode
           -> ATerm Loc FreeVarName
           -> Environment FreeVarName
           -> Either Error (TypeScheme Pos)
inferATerm isRec loc fv im tm env = do
  trace <- inferATermTraced isRec loc fv im tm env
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
    False -> Left (OtherError (T.unlines [ "Annotated type is not subsumed by inferred type"
                                         , " Annotated type: " <> ppPrint tyAnnot
                                         , " Inferred type:  " <> ppPrint ty]))

insertDecl :: Declaration FreeVarName Loc
           -> Environment FreeVarName
           -> InferenceMode
           -> Either LocatedError (Environment FreeVarName)
insertDecl (PrdDecl isRec loc v annot loct)  env@Environment { prdEnv } im = do
  ty <- first (Located loc) (inferSTerm isRec loc v im PrdRep loct env)
  ty <- first (Located loc) (checkAnnot ty annot)
  return $ env { prdEnv  = M.insert v (first (const ()) loct, loc, ty) prdEnv }
insertDecl (CnsDecl isRec loc v annot loct)  env@Environment { cnsEnv } im = do
  ty <- first (Located loc) (inferSTerm isRec loc v im CnsRep loct env)
  ty <- first (Located loc) (checkAnnot ty annot)
  return $ env { cnsEnv  = M.insert v (first (const ()) loct, loc, ty) cnsEnv }
insertDecl (CmdDecl loc v loct)  env@Environment { cmdEnv } im = do
  _ <- first (Located loc) $ checkCmd loct env im
  return $ env { cmdEnv  = M.insert v (first (const ()) loct, loc) cmdEnv }
insertDecl (DefDecl isRec loc v annot t)  env@Environment { defEnv } im = do
  ty <- first (Located loc) (inferATerm isRec loc v im t env)
  ty <- first (Located loc) (checkAnnot ty annot)
  return $ env { defEnv  = M.insert v (first (const ()) t, loc, ty) defEnv }
insertDecl (DataDecl _loc dcl) env@Environment { declEnv } _ = do
  return $ env { declEnv = dcl : declEnv }
insertDecl ParseErrorDecl _ _ = error "Should not occur: Tried to insert ParseErrorDecl into Environment"

inferProgram :: [Declaration FreeVarName Loc] -> InferenceMode -> Either LocatedError (Environment FreeVarName)
inferProgram = inferProgram' mempty
  where
    inferProgram' :: Environment FreeVarName
                  -> [Declaration FreeVarName Loc]
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
             -> Declaration FreeVarName Loc
             -> Environment FreeVarName
             -> IO (Maybe (Environment FreeVarName))
insertDeclIO verb im (PrdDecl isRec loc v annot loct)  env@Environment { prdEnv }  = do
  case inferSTermTraced isRec loc v im PrdRep loct env of
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
          let newEnv = env { prdEnv  = M.insert v ( first (const ()) loct ,loc, ty) prdEnv }
          putStr "Inferred type: "
          ppPrintIO (trace_resType trace)
          return (Just newEnv)
insertDeclIO verb im (CnsDecl isRec loc v annot loct)  env@Environment { cnsEnv }  = do
  case inferSTermTraced isRec loc v im CnsRep loct env of
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
          let newEnv = env { cnsEnv  = M.insert v (first (const ()) loct, loc, ty) cnsEnv }
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
      return (Just (env { cmdEnv  = M.insert v (first (const ()) loct, loc) cmdEnv }))
insertDeclIO verb im (DefDecl isRec loc v annot t)  env@Environment { defEnv }  = do
  case inferATermTraced isRec loc v im t env of
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
          let newEnv = env { defEnv  = M.insert v (first (const ()) t, loc,ty) defEnv }
          putStr "Inferred type: "
          ppPrintIO (trace_resType trace)
          return (Just newEnv)
insertDeclIO _ _ (DataDecl _loc dcl) env@Environment { declEnv } = do
  return (Just (env { declEnv = dcl : declEnv }))
insertDeclIO _ _ ParseErrorDecl _ = error "Should not occur: Tried to insert ParseErrorDecl into Environment"