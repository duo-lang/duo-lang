module Eval.Eval
  ( eval
  , evalSteps
  ) where

import Control.Monad.Except
import Data.Text qualified as T

import Driver.Environment (Environment)
import Errors
import Lookup
import Pretty.Pretty
import Pretty.Terms ()
import Syntax.Common
import Syntax.AST.Terms
import Eval.Definition
import Eval.Primitives
import Utils

---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

-- | Returns Nothing if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalTermOnce :: Command -> EvalM (Maybe Command)
evalTermOnce (ExitSuccess _) = return Nothing
evalTermOnce (ExitFailure _) = return Nothing
evalTermOnce (Print _ prd cmd) = do
  liftIO $ ppPrintIO prd
  return (Just cmd)
evalTermOnce (Read _ cns) = do
  tm <- liftIO $ readInt
  return (Just (Apply defaultLoc (Just (CBox CBV)) tm cns))
evalTermOnce (Jump _ fv) = do
  cmd <- lookupCommand fv
  return (Just cmd)
evalTermOnce (Apply _ Nothing _ _) = throwEvalError ["Tried to evaluate command which was not correctly kind annotated (Nothing)"]
evalTermOnce (Apply _ (Just kind) prd cns) = evalApplyOnce kind prd cns
evalTermOnce (PrimOp _ pt op args) = evalPrimOp pt op args

evalApplyOnce :: MonoKind -> Term Prd -> Term Cns -> EvalM  (Maybe Command)
-- Free variables have to be looked up in the environment.
evalApplyOnce kind (FreeVar _ PrdRep _ fv) cns = do
  (prd,_) <- lookupTerm PrdRep fv
  return (Just (Apply defaultLoc (Just kind) prd cns))
evalApplyOnce kind prd (FreeVar _ CnsRep _ fv) = do
  (cns,_) <- lookupTerm CnsRep fv
  return (Just (Apply defaultLoc (Just kind) prd cns))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce _ prd@(Xtor _ PrdRep _ _ xt args) cns@(XMatch _ CnsRep _ _ cases) = do
  (MkCmdCase _ _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply defaultLoc Nothing prd cns) argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalApplyOnce _ prd@(XMatch _ PrdRep _ _ cases) cns@(Xtor _ CnsRep _ _ xt args) = do
  (MkCmdCase _ _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply defaultLoc Nothing prd cns) argTypes args
  return (Just (commandOpening args cmd')) --reduction is just opening
-- Mu abstractions have to be evaluated while taking care of evaluation order.
evalApplyOnce (CBox CBV) (MuAbs _ PrdRep _ _ cmd) cns@(MuAbs _ CnsRep _ _ _) =
  return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce (CRep _) (MuAbs _ PrdRep _ _ cmd) cns@(MuAbs _ CnsRep _ _ _) =
  return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce (CBox CBN) prd@(MuAbs _ PrdRep _ _ _) (MuAbs _ CnsRep _ _ cmd) =
  return (Just (commandOpening [PrdTerm prd] cmd))
evalApplyOnce _ (MuAbs _ PrdRep _ _ cmd) cns = return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce _ prd (MuAbs _ CnsRep _ _ cmd) = return (Just (commandOpening [PrdTerm prd] cmd))
-- Bound variables should not occur at the toplevel during evaluation.
evalApplyOnce _ (BoundVar _ PrdRep _ i) _ = throwEvalError ["Found bound variable during evaluation. Index: " <> T.pack (show i)]
evalApplyOnce _ _ (BoundVar _ CnsRep _ i) = throwEvalError [ "Found bound variable during evaluation. Index: " <> T.pack (show i)]
-- Match applied to Match, or Xtor to Xtor can't evaluate
evalApplyOnce _ XMatch{} XMatch{} = throwEvalError ["Cannot evaluate match applied to match"]
evalApplyOnce _ Xtor{} Xtor{} = throwEvalError ["Cannot evaluate constructor applied to destructor"]
evalApplyOnce _ _ _ = throwEvalError ["Cannot evaluate, probably an asymmetric term..."]

-- | Return just the final evaluation result
evalM :: Command -> EvalM Command
evalM cmd = do
  cmd' <- evalTermOnce cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> evalM cmd'

-- | Return all intermediate evaluation results
evalStepsM :: Command -> EvalM [Command]
evalStepsM cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: [Command] -> Command -> EvalM [Command]
    evalSteps' cmds cmd = do
      cmd' <- evalTermOnce cmd
      case cmd' of
        Nothing -> return cmds
        Just cmd' -> evalSteps' (cmds ++ [cmd']) cmd'

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

eval :: Command -> Environment -> IO (Either Error Command)
eval cmd env = runEval (evalM cmd) env

evalSteps :: Command -> Environment -> IO (Either Error [Command])
evalSteps cmd env = runEval (evalStepsM cmd) env
