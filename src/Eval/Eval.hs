module Eval.Eval
  ( eval
  , evalSteps
  ) where

import Control.Monad.Except
import Data.Text qualified as T
import Data.List.NonEmpty ( NonEmpty )

import Errors
import Pretty.Pretty
import Syntax.CST.Kinds
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.Core.Annot
import Syntax.TST.Terms
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
  tm <- liftIO readInt
  return (Just (Apply defaultLoc ApplyAnnotOrig (Just (CBox CBV)) tm cns))
evalTermOnce (Jump _ fv) = do
  cmd <- lookupCommand fv
  return (Just cmd)
evalTermOnce Method {} = return Nothing
  -- throwEvalError defaultLoc ["Eval for type class methods not implemented yet."]
evalTermOnce (Apply _ _ Nothing _ _) =
  throwEvalError defaultLoc ["Tried to evaluate command which was not correctly kind annotated (Nothing)"]
evalTermOnce (Apply _ _ (Just (KindVar _)) _ _) = throwEvalError defaultLoc ["Tried to evaluate command which was not correctly kind annotated (KindVar)"]
evalTermOnce (Apply _ _ (Just kind) prd cns) = evalApplyOnce kind prd cns
evalTermOnce (PrimOp _ op args) = evalPrimOp op args

evalApplyOnce :: MonoKind -> Term Prd -> Term Cns -> EvalM  (Maybe Command)
-- Free variables have to be looked up in the environment.
evalApplyOnce kind (FreeVar _ PrdRep _ fv) cns = do
  prd <- lookupTerm PrdRep fv
  return (Just (Apply defaultLoc ApplyAnnotOrig (Just kind) prd cns))
evalApplyOnce kind prd (FreeVar _ CnsRep _ fv) = do
  cns <- lookupTerm CnsRep fv
  return (Just (Apply defaultLoc ApplyAnnotOrig (Just kind) prd cns))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce _ prd@(Xtor _ _ PrdRep _ _ xt args) cns@(XCase _ _ CnsRep _ _ cases) = do
  (MkCmdCase _ (XtorPat _ _ argTypes) cmd') <- lookupMatchCase xt cases
  checkArgs (Apply defaultLoc ApplyAnnotOrig Nothing prd cns) argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalApplyOnce _ prd@(XCase _ _ PrdRep _ _  cases) cns@(Xtor _ _ CnsRep _ _ xt args) = do
  (MkCmdCase _ (XtorPat _ _ argTypes) cmd') <- lookupMatchCase xt cases
  checkArgs (Apply defaultLoc ApplyAnnotOrig Nothing prd cns) argTypes args
  return (Just (commandOpening args cmd')) --reduction is just opening
-- Mu abstractions have to be evaluated while taking care of evaluation order.
evalApplyOnce (CBox CBV) (MuAbs _ _ PrdRep _ _ cmd) cns@(MuAbs _ _ CnsRep _ _ _) =
  return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce I64Rep (MuAbs _ _ PrdRep _ _ cmd) cns@(MuAbs _ _ CnsRep _ _ _) =
  return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce F64Rep (MuAbs _ _ PrdRep _ _ cmd) cns@(MuAbs _ _ CnsRep _ _ _) =
  return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce CharRep (MuAbs _ _ PrdRep _ _ cmd) cns@(MuAbs _ _ CnsRep _ _ _) =
  return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce StringRep (MuAbs _ _ PrdRep _ _ cmd) cns@(MuAbs _ _ CnsRep _ _ _) =
  return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce (CBox CBN) prd@(MuAbs _ _ PrdRep _ _ _) (MuAbs _ _ CnsRep _ _ cmd) =
  return (Just (commandOpening [PrdTerm prd] cmd))
evalApplyOnce _ (MuAbs _ _ PrdRep _ _ cmd) cns =
  return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce _ prd (MuAbs _ _ CnsRep _ _ cmd) =
  return (Just (commandOpening [PrdTerm prd] cmd))
-- Bound variables should not occur at the toplevel during evaluation.
evalApplyOnce _ (BoundVar _ PrdRep _ i) _ =
  throwEvalError defaultLoc ["Found bound variable during evaluation. Index: " <> T.pack (show i)]
evalApplyOnce _ _ (BoundVar _ CnsRep _ i) =
  throwEvalError defaultLoc [ "Found bound variable during evaluation. Index: " <> T.pack (show i)]
-- Everything else should be excluded by typechecking
evalApplyOnce _ prd cns =
  throwEvalError defaultLoc [ "Cannot evaluate."
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

eval :: Command -> EvalEnv -> IO (Either (NonEmpty Error) Command)
eval cmd = runEval (evalM cmd)

evalSteps :: Command -> EvalEnv -> IO (Either (NonEmpty Error) [Command])
evalSteps cmd = runEval (evalStepsM cmd)
