module Eval.Eval
  ( eval
  , evalSteps
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Data.List (find)
import Data.Text qualified as T

import Errors
import Lookup
import Pretty.Pretty
import Pretty.Terms ()
import Syntax.Program (Environment)
import Syntax.Kinds (CallingConvention(..))
import Syntax.CommonTerm
import Syntax.Terms
import Translate.Desugar
import Translate.Focusing

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

newtype EvalM a = EvalM { unEvalM :: ReaderT (Environment, CallingConvention) (ExceptT Error IO) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader (Environment, CallingConvention))

runEval :: EvalM a -> CallingConvention -> Environment -> IO (Either Error a)
runEval e evalorder env = runExceptT (runReaderT (unEvalM e) (env,evalorder))

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

lookupEvalOrder :: EvalM CallingConvention 
lookupEvalOrder = asks snd



lookupMatchCase :: XtorName -> [CmdCase Compiled] -> EvalM (CmdCase Compiled)
lookupMatchCase xt cases = case find (\MkCmdCase { cmdcase_name } -> xt == cmdcase_name) cases of
  Just pmcase -> return pmcase
  Nothing -> throwEvalError ["Error during evaluation. The xtor: "
                            , unXtorName xt
                            , "doesn't occur in match."
                            ]

checkArgs :: Command Compiled -> [(PrdCns,a)] -> Substitution Compiled -> EvalM ()
checkArgs _md [] [] = return ()
checkArgs cmd ((Prd,_):rest1) (PrdTerm _:rest2) = checkArgs cmd rest1 rest2
checkArgs cmd ((Cns,_):rest1) (CnsTerm _:rest2) = checkArgs cmd rest1 rest2
checkArgs cmd _ _ = throwEvalError [ "Error during evaluation of:"
                                   , ppPrint cmd
                                   , "Argument lengths don't coincide."
                                   ]

---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

-- | Returns Notihng if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalTermOnce :: Command Compiled -> EvalM (Maybe (Command Compiled))
evalTermOnce (Done _) = return Nothing
evalTermOnce (Print _ _) = return Nothing
evalTermOnce (Apply _ _ prd cns) = evalApplyOnce prd cns

evalApplyOnce :: Term Prd Compiled -> Term Cns Compiled -> EvalM  (Maybe (Command Compiled))
-- Free variables have to be looked up in the environment.
evalApplyOnce (FreeVar _ PrdRep fv) cns = do
  (prd,_) <- lookupSTerm PrdRep fv
  eo <- lookupEvalOrder
  return (Just (Apply () Nothing (focusTerm eo (desugarTerm prd)) cns))
evalApplyOnce prd (FreeVar _ CnsRep fv) = do
  (cns,_) <- lookupSTerm CnsRep fv
  eo <- lookupEvalOrder
  return (Just (Apply () Nothing prd (focusTerm eo (desugarTerm cns))))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce prd@(XtorCall _ PrdRep xt args) cns@(XMatch _ CnsRep _ cases) = do
  (MkCmdCase _ _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply () Nothing prd cns) argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalApplyOnce prd@(XMatch _ PrdRep _ cases) cns@(XtorCall _ CnsRep xt args) = do
  (MkCmdCase _ _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply () Nothing prd cns) argTypes args
  return (Just (commandOpening args cmd')) --reduction is just opening
-- Mu abstractions have to be evaluated while taking care of evaluation order.
evalApplyOnce prd@(MuAbs _ PrdRep _ cmd) cns@(MuAbs _ CnsRep _ cmd') = do
  order <- lookupEvalOrder
  case order of
    CBV -> return (Just (commandOpening [CnsTerm cns] cmd))
    CBN -> return (Just (commandOpening [PrdTerm prd] cmd'))
evalApplyOnce (MuAbs _ PrdRep _ cmd) cns = return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce prd (MuAbs _ CnsRep _ cmd) = return (Just (commandOpening [PrdTerm prd] cmd))
-- Bound variables should not occur at the toplevel during evaluation.
evalApplyOnce (BoundVar _ PrdRep i) _ = throwEvalError ["Found bound variable during evaluation. Index: " <> T.pack (show i)]
evalApplyOnce _ (BoundVar _ CnsRep i) = throwEvalError [ "Found bound variable during evaluation. Index: " <> T.pack (show i)]
-- Match applied to Match, or Xtor to Xtor can't evaluate
evalApplyOnce XMatch{} XMatch{} = throwEvalError ["Cannot evaluate match applied to match"]
evalApplyOnce XtorCall{} XtorCall{} = throwEvalError ["Cannot evaluate constructor applied to destructor"]
evalApplyOnce _ _ = throwEvalError ["Cannot evaluate, probably an asymmetric term..."]


-- | Return just the final evaluation result
evalM :: Command Compiled -> EvalM (Command Compiled)
evalM cmd = do
  cmd' <- evalTermOnce cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> evalM cmd'

-- | Return all intermediate evaluation results
evalStepsM :: Command Compiled -> EvalM [Command Compiled]
evalStepsM cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: [Command Compiled] -> Command Compiled -> EvalM [Command Compiled]
    evalSteps' cmds cmd = do
      cmd' <- evalTermOnce cmd
      case cmd' of
        Nothing -> return cmds
        Just cmd' -> evalSteps' (cmds ++ [cmd']) cmd'

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

eval :: Command Compiled -> CallingConvention -> Environment -> IO (Either Error (Command Compiled))
eval cmd cc env = runEval (evalM  (focusCmd cc cmd)) cc env

evalSteps :: Command Compiled -> CallingConvention -> Environment -> IO (Either Error [Command Compiled])
evalSteps cmd cc env = runEval (evalStepsM (focusCmd cc cmd)) cc env