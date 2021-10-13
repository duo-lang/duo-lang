module TypeInference.InferProgram
  ( TypeInferenceTrace (..)
  , InferenceOptions(..)
  , defaultInferenceOptions
    -- Symmetric Terms and Commands
  , inferSTermTraced
  , inferSTerm
  , checkCmd
    -- Asymmetric terms
  , inferATerm
  , inferATermTraced
  ) where

import Control.Monad (when, forM)
import Data.Bifunctor (first)
import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist )

import Errors ( LocatedError, Error(OtherError) )
import Pretty.Pretty ( ppPrint, ppPrintIO )
import Pretty.Errors ( printLocatedError )
import Syntax.ATerms ( FreeVarName, PrdCnsRep(..), ATerm )
import Syntax.STerms ( Command, STerm )
import Syntax.Types
    ( SolverResult,
      ConstraintSet,
      TypeScheme,
      Typ,
      PolarityRep(PosRep),
      Polarity(Pos) )
import TypeAutomata.Definition ( TypeAutDet, TypeAut )
import Syntax.Program
    ( Environment(..),
      Declaration(..),
      IsRec(..),
      ModuleName(..) )
import Utils ( Verbosity(..), Located(Located), Loc )

import TypeAutomata.ToAutomaton ( solverStateToTypeAut )
import TypeAutomata.Determinize ( determinize )
import TypeAutomata.Lint (lint)
import TypeAutomata.Minimize ( minimize )
import TypeAutomata.FromAutomaton ( autToType )
import TypeAutomata.RemoveAdmissible ( removeAdmissableFlowEdges )
import TypeAutomata.Subsume (subsume)
import TypeInference.GenerateConstraints.Definition
    ( PrdCnsToPol, prdCnsToPol, InferenceMode(..), runGenM )
import TypeInference.GenerateConstraints.ATerms
    ( genConstraintsATerm, genConstraintsATermRecursive )
import TypeInference.GenerateConstraints.STerms
    ( genConstraintsSTerm,
      genConstraintsCommand,
      genConstraintsSTermRecursive )
import TypeInference.SolveConstraints (solveConstraints)
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )

------------------------------------------------------------------------------
-- Typeinference Options
------------------------------------------------------------------------------

data InferenceOptions = InferenceOptions
  { infOptsVerbosity :: Verbosity
  , infOptsMode :: InferenceMode
  , infOptsLibPath :: [FilePath]
  }

defaultInferenceOptions :: InferenceOptions
defaultInferenceOptions = InferenceOptions Silent InferNominal []

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
                 -> InferenceOptions
                 -> PrdCnsRep pc -> STerm pc Loc FreeVarName
                 -> Environment FreeVarName
                 -> Either Error (TypeInferenceTrace (PrdCnsToPol pc))
inferSTermTraced isRec loc fv infopts rep tm env = do
  let genFun = case isRec of
        Recursive -> genConstraintsSTermRecursive loc fv rep tm
        NonRecursive -> genConstraintsSTerm tm
  ((_,ty), constraintSet) <- runGenM env (infOptsMode infopts) genFun
  solverState <- solveConstraints constraintSet env (infOptsMode infopts)
  generateTypeInferenceTrace (prdCnsToPol rep) constraintSet solverState ty

inferSTerm :: IsRec
           -> Loc
           -> FreeVarName
           -> InferenceOptions
           -> PrdCnsRep pc -> STerm pc Loc FreeVarName
           -> Environment FreeVarName
           -> Either Error (TypeScheme (PrdCnsToPol pc))
inferSTerm isRec loc fv infopts rep tm env = do
  trace <- inferSTermTraced isRec loc fv infopts rep tm env
  return $ trace_resType trace

checkCmd :: Command Loc FreeVarName
         -> Environment FreeVarName
         -> InferenceOptions
         -> Either Error (ConstraintSet, SolverResult)
checkCmd cmd env infopts = do
  constraints <- snd <$> runGenM env (infOptsMode infopts) (genConstraintsCommand cmd)
  solverResult <- solveConstraints constraints env (infOptsMode infopts)
  return (constraints, solverResult)

------------------------------------------------------------------------------
-- ASymmetric Terms
------------------------------------------------------------------------------

inferATermTraced :: IsRec
                 -> Loc
                 -> FreeVarName
                 -> InferenceOptions
                 -> ATerm Loc FreeVarName
                 -> Environment FreeVarName
                 -> Either Error (TypeInferenceTrace Pos)
inferATermTraced isRec loc fv infopts tm env = do
  let genFun = case isRec of
        Recursive -> genConstraintsATermRecursive loc fv tm
        NonRecursive -> genConstraintsATerm tm
  ((_, ty), constraintSet) <- runGenM env (infOptsMode infopts) genFun
  solverState <- solveConstraints constraintSet env (infOptsMode infopts)
  generateTypeInferenceTrace PosRep constraintSet solverState ty

inferATerm :: IsRec
           -> Loc
           -> FreeVarName
           -> InferenceOptions
           -> ATerm Loc FreeVarName
           -> Environment FreeVarName
           -> Either Error (TypeScheme Pos)
inferATerm isRec loc fv infopts tm env = do
  trace <- inferATermTraced isRec loc fv infopts tm env
  return $ trace_resType trace

------------------------------------------------------------------------------
-- Programs
------------------------------------------------------------------------------



