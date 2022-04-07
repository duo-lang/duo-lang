module Eval.Eval
  ( eval
  , evalSteps
  ) where

import Control.Monad.Except
import Data.Text qualified as T

import Errors
import Pretty.Pretty
import Pretty.Terms ()
import Syntax.Common
import Syntax.Core.Terms
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
evalApplyOnce kind (FreeVar _ PrdRep fv) cns = do
  prd <- lookupTerm PrdRep fv
  return (Just (Apply defaultLoc (Just kind) prd cns))
evalApplyOnce kind prd (FreeVar _ CnsRep fv) = do
  cns <- lookupTerm CnsRep fv
  return (Just (Apply defaultLoc (Just kind) prd cns))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce _ prd@(Xtor _ PrdRep _ xt args) cns@(XMatch _ CnsRep _ cases) = do
  (MkCmdCase _ _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply defaultLoc Nothing prd cns) argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalApplyOnce _ prd@(XMatch _ PrdRep _ cases) cns@(Xtor _ CnsRep _ xt args) = do
  (MkCmdCase _ _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply defaultLoc Nothing prd cns) argTypes args
  return (Just (commandOpening args cmd')) --reduction is just opening
-- Mu abstractions have to be evaluated while taking care of evaluation order.
evalApplyOnce (CBox CBV) (MuAbs _ PrdRep _ cmd) cns@(MuAbs _ CnsRep _ _) =
  return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce (CRep _) (MuAbs _ PrdRep _ cmd) cns@(MuAbs _ CnsRep _ _) =
  return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce (CBox CBN) prd@(MuAbs _ PrdRep _ _) (MuAbs _ CnsRep _ cmd) =
  return (Just (commandOpening [PrdTerm prd] cmd))
evalApplyOnce _ (MuAbs _ PrdRep _ cmd) cns =
  return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce _ prd (MuAbs _ CnsRep _ cmd) =
  return (Just (commandOpening [PrdTerm prd] cmd))
-- Bound variables should not occur at the toplevel during evaluation.
evalApplyOnce _ (BoundVar _ PrdRep i) _ =
  throwEvalError ["Found bound variable during evaluation. Index: " <> T.pack (show i)]
evalApplyOnce _ _ (BoundVar _ CnsRep i) =
  throwEvalError [ "Found bound variable during evaluation. Index: " <> T.pack (show i)]
-- Everything else should be excluded by typechecking
evalApplyOnce _ prd cns =
  throwEvalError [ "Cannot evaluate."
                 , "Producer: " <> ppPrint prd
                 , "Consumer:"  <> ppPrint cns
                 ]

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

eval :: Command -> EvalEnv -> IO (Either Error Command)
eval cmd env = runEval (evalM cmd) env

evalSteps :: Command -> EvalEnv -> IO (Either Error [Command])
evalSteps cmd env = runEval (evalStepsM cmd) env
