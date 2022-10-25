{-# LANGUAGE UndecidableInstances #-}
module Eval.Eval
  ( eval
  , evalSteps
  , EvalMWrapper(..)
  ) where

import Control.Monad.Except
import Data.Text qualified as T
import Data.List.NonEmpty ( NonEmpty )

import Errors
import Pretty.Pretty
import Syntax.CST.Kinds
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.Core.Annot
import Syntax.Core.Terms (Pattern(..))
import Syntax.TST.Terms
import Eval.Definition
import Eval.Primitives
import Loc
import qualified Syntax.LocallyNameless as LN
import Control.Monad.Writer (MonadWriter)
import Control.Monad.State (MonadState (..))

class EvalMonad m where
  printM   :: PrettyAnn a => a -> EvalM m ()
  readM    :: EvalM m (Term 'Prd)
  failM    :: EvalM m ()
  successM :: EvalM m ()

instance EvalMonad IO where
  printM   = liftIO . ppPrintIO
  readM    = liftIO readInt
  failM    = liftIO (ppPrintIO $ ExitFailure defaultLoc)
  successM = liftIO (ppPrintIO $ ExitSuccess defaultLoc)

-- this wrapper is only needed to avoid overlapping EvalMonad instances for IO
newtype EvalMWrapper m a = MkEvalMWrapper { unEvalMWrapper :: m a }
  deriving newtype (Functor, Applicative, Monad, MonadWriter w, MonadState s, MonadIO)

instance (MonadState [Int] m, MonadWriter [String] m) => EvalMonad (EvalMWrapper m) where
  printM = ppPrintWriter
  readM  = do
    is <- get
    case is of
      []      -> return $ convertInt 0
      (i:is)  -> do
        put is
        return $ convertInt i
  failM    = ppPrintWriter $ ExitFailure defaultLoc
  successM = ppPrintWriter $ ExitSuccess defaultLoc

---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

-- | Returns Nothing if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalTermOnce :: (Monad m, EvalMonad m) => Command -> EvalM m (Maybe Command)
evalTermOnce (ExitSuccess _) = successM >> return Nothing
evalTermOnce (ExitFailure _) = failM >> return Nothing
evalTermOnce (Print _ prd cmd) = do
  printM prd
  return (Just cmd)
evalTermOnce (Read _ cns) = do
  tm <- readM
  return (Just (Apply defaultLoc ApplyAnnotOrig (CBox CBV) tm cns))
evalTermOnce (Jump _ fv) = do
  cmd <- lookupCommand fv
  return (Just cmd)
evalTermOnce Method {} = return Nothing
  -- throwEvalError defaultLoc ["Eval for type class methods not implemented yet."]
evalTermOnce (Apply _ _ kind prd cns) = evalApplyOnce kind prd cns
evalTermOnce (PrimOp _ op args) = evalPrimOp op args

evalApplyOnce :: Monad m => MonoKind -> Term Prd -> Term Cns -> EvalM m  (Maybe Command)
-- Free variables have to be looked up in the environment.
evalApplyOnce kind (FreeVar _ PrdRep _ fv) cns = do
  prd <- lookupTerm PrdRep fv
  return (Just (Apply defaultLoc ApplyAnnotOrig kind prd cns))
evalApplyOnce kind prd (FreeVar _ CnsRep _ fv) = do
  cns <- lookupTerm CnsRep fv
  return (Just (Apply defaultLoc ApplyAnnotOrig kind prd cns))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce _ prd@(Xtor _ _ PrdRep _ _ xt args) cns@(XCase _ _ CnsRep _ _ cases) = do
  (MkCmdCase _ (XtorPat _ _ argTypes) cmd') <- lookupMatchCase xt cases
  checkArgs (Apply defaultLoc ApplyAnnotOrig (error "evalApplyOnce: This Kind should never be used") prd cns) argTypes args
  return (Just  (LN.open args cmd')) --reduction is just opening
evalApplyOnce _ prd@(XCase _ _ PrdRep _ _  cases) cns@(Xtor _ _ CnsRep _ _ xt args) = do
  (MkCmdCase _ (XtorPat _ _ argTypes) cmd') <- lookupMatchCase xt cases
  checkArgs (Apply defaultLoc ApplyAnnotOrig (error "evalApplyOnce: This Kind should never be used") prd cns) argTypes args
  return (Just (LN.open args cmd')) --reduction is just opening
-- Mu abstractions have to be evaluated while taking care of evaluation order.
evalApplyOnce (CBox CBV) (MuAbs _ _ PrdRep _ _ cmd) cns@(MuAbs _ _ CnsRep _ _ _) =
  return (Just (LN.open (MkSubstitution [CnsTerm cns]) cmd))
evalApplyOnce I64Rep (MuAbs _ _ PrdRep _ _ cmd) cns@(MuAbs _ _ CnsRep _ _ _) =
  return (Just (LN.open (MkSubstitution [CnsTerm cns]) cmd))
evalApplyOnce F64Rep (MuAbs _ _ PrdRep _ _ cmd) cns@(MuAbs _ _ CnsRep _ _ _) =
  return (Just (LN.open (MkSubstitution [CnsTerm cns]) cmd))
evalApplyOnce CharRep (MuAbs _ _ PrdRep _ _ cmd) cns@(MuAbs _ _ CnsRep _ _ _) =
  return (Just (LN.open (MkSubstitution [CnsTerm cns]) cmd))
evalApplyOnce StringRep (MuAbs _ _ PrdRep _ _ cmd) cns@(MuAbs _ _ CnsRep _ _ _) =
  return (Just (LN.open (MkSubstitution [CnsTerm cns]) cmd))
evalApplyOnce (CBox CBN) prd@(MuAbs _ _ PrdRep _ _ _) (MuAbs _ _ CnsRep _ _ cmd) =
  return (Just (LN.open (MkSubstitution [PrdTerm prd]) cmd))
evalApplyOnce _ (MuAbs _ _ PrdRep _ _ cmd) cns =
  return (Just (LN.open (MkSubstitution [CnsTerm cns]) cmd))
evalApplyOnce _ prd (MuAbs _ _ CnsRep _ _ cmd) =
  return (Just (LN.open (MkSubstitution [PrdTerm prd]) cmd))
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
evalM :: (Monad m, EvalMonad m) => Command -> EvalM m Command
evalM cmd = do
  cmd' <- evalTermOnce cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> evalM cmd'

-- | Return all intermediate evaluation results
evalStepsM :: (Monad m, EvalMonad m) => Command -> EvalM m [Command]
evalStepsM cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: (Monad m, EvalMonad m) => [Command] -> Command -> EvalM m [Command]
    evalSteps' cmds cmd = do
      cmd' <- evalTermOnce cmd
      case cmd' of
        Nothing -> return cmds
        Just cmd' -> evalSteps' (cmds ++ [cmd']) cmd'

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

eval :: (Monad m, EvalMonad m) => Command -> EvalEnv -> m (Either (NonEmpty Error) Command)
eval cmd = runEval (evalM cmd)

evalSteps :: (Monad m, EvalMonad m) => Command -> EvalEnv -> m (Either (NonEmpty Error) [Command])
evalSteps cmd = runEval (evalStepsM cmd)
