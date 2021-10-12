module TypeInference.InferProgram
  ( TypeInferenceTrace (..)
    -- Symmetric Terms and Commands
  , inferSTermTraced
  , inferSTerm
    -- Asymmetric terms
  , inferATerm
    -- Declarations and Programs
  , insertDecl
  , inferProgram
  ) where

import Control.Monad (when)
import Data.Bifunctor (first)
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as T

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
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )

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

checkAnnot :: TypeScheme pol -- ^ Inferred type
           -> (Maybe (TypeScheme pol)) -- ^ Annotated type
           -> Either Error (TypeScheme pol)
checkAnnot tyInferred Nothing = return tyInferred
checkAnnot tyInferred (Just tyAnnotated) = do
  isSubsumed <- subsume tyInferred tyAnnotated
  if isSubsumed
    then return tyAnnotated
    else Left (OtherError (T.unlines [ "Annotated type is not subsumed by inferred type"
                                     , " Annotated type: " <> ppPrint tyAnnotated
                                     , " Inferred type:  " <> ppPrint tyInferred
                                     ]))


insertDecl :: Verbosity
           -> InferenceMode
           -> Declaration FreeVarName Loc
           -> Environment FreeVarName
           -> IO (Either LocatedError (Environment FreeVarName))
insertDecl verb im (PrdDecl isRec loc v annot loct)  env@Environment { prdEnv }  = do
  case inferSTermTraced isRec loc v im PrdRep loct env of
    Left err -> do
      let locerr = Located loc err
      printLocatedError locerr
      return (Left locerr)
    Right trace -> do
      when (verb == Verbose) $ do
        ppPrintIO (trace_constraintSet trace)
        ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation
      let ty = trace_resType trace
      case checkAnnot ty annot of
        Left err -> do
           ppPrintIO err
           return (Left (Located loc err))
        Right ty -> do
          let newEnv = env { prdEnv  = M.insert v ( first (const ()) loct ,loc, ty) prdEnv }
          putStr "Inferred type: "
          ppPrintIO (trace_resType trace)
          return (Right newEnv)
insertDecl verb im (CnsDecl isRec loc v annot loct)  env@Environment { cnsEnv }  = do
  case inferSTermTraced isRec loc v im CnsRep loct env of
    Left err -> do
      let locerr = Located loc err
      printLocatedError locerr
      return (Left locerr)
    Right trace -> do
      when (verb == Verbose) $ do
        ppPrintIO (trace_constraintSet trace)
        ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation:
      let ty = trace_resType trace
      case checkAnnot ty annot of
        Left err -> do
          ppPrintIO err
          return (Left (Located loc err))
        Right ty -> do
          let newEnv = env { cnsEnv  = M.insert v (first (const ()) loct, loc, ty) cnsEnv }
          putStr "Inferred type: "
          ppPrintIO (trace_resType trace)
          return (Right newEnv)
insertDecl verb im (CmdDecl loc v loct)  env@Environment { cmdEnv }  = do
  case checkCmd loct env im of
    Left err -> do
      let locerr = Located loc err
      printLocatedError locerr
      return (Left locerr)
    Right (constraints, solverResult) -> do
      when (verb == Verbose) $ do
        ppPrintIO constraints
        ppPrintIO solverResult
      return (Right (env { cmdEnv  = M.insert v (first (const ()) loct, loc) cmdEnv }))
insertDecl verb im (DefDecl isRec loc v annot t)  env@Environment { defEnv }  = do
  case inferATermTraced isRec loc v im t env of
    Left err -> do
      let locerr = Located loc err
      printLocatedError locerr
      return (Left locerr)
    Right trace -> do
      when (verb == Verbose) $ do
        ppPrintIO (trace_constraintSet trace)
        ppPrintIO (trace_solvedConstraints trace)
      -- Check annotation
      let ty = trace_resType trace
      case checkAnnot ty annot of
        Left err -> do
          ppPrintIO err
          return (Left (Located loc err))
        Right ty -> do
          let newEnv = env { defEnv  = M.insert v (first (const ()) t, loc,ty) defEnv }
          putStr "Inferred type: "
          ppPrintIO (trace_resType trace)
          return (Right newEnv)
insertDecl _ _ (DataDecl _loc dcl) env@Environment { declEnv } = do
  return (Right (env { declEnv = dcl : declEnv }))
insertDecl vb im (ImportDecl _loc (ModuleName mod)) env = do
  let fp = T.unpack mod <> ".ds"
  env' <- inferProgramFromDisk vb im fp
  case env' of
    Left err -> return (Left err)
    Right env' -> return (Right (env <> env'))
insertDecl _ _ ParseErrorDecl _ = error "Should not occur: Tried to insert ParseErrorDecl into Environment"



inferProgramFromDisk :: Verbosity
                     -> InferenceMode
                     -> FilePath 
                     -> IO (Either LocatedError (Environment FreeVarName ))
inferProgramFromDisk vb im fp = do
  file <- T.readFile fp
  let parsed = runFileParser fp programP file
  case parsed of
    Left _err -> return (Left (Located undefined undefined))
    Right decls -> inferProgram vb im decls

inferProgram :: Verbosity
             -> InferenceMode
             -> [Declaration FreeVarName Loc]
             -> IO (Either LocatedError (Environment FreeVarName))
inferProgram vb im decls = inferProgram' mempty decls
 where
   inferProgram' :: Environment FreeVarName
                 -> [Declaration FreeVarName Loc]
                 -> IO (Either LocatedError (Environment FreeVarName))
   inferProgram' env [] = return (Right env)
   inferProgram' env (decl:decls) = do
     env' <- insertDecl vb im decl env
     case env' of
       Left err -> return (Left err)
       Right env'' -> inferProgram' env'' decls


