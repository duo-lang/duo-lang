module Eval.STerms
  ( eval
  , evalSteps
  ) where

import Data.List (find)
import Prettyprinter

import Pretty.Pretty
import Eval.Eval
import Syntax.STerms
import Utils

---------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------

lookupCase :: XtorName -> [SCase a] -> EvalM (SCase a)
lookupCase xt cases = case find (\MkSCase { scase_name } -> xt == scase_name) cases of
  Just pmcase -> return pmcase
  Nothing -> throwEvalError $ unlines ["Error during evaluation. The xtor: "
                                      , unXtorName xt
                                      , "doesn't occur in match."
                                      ]

lengthXtorArgs :: XtorArgs a -> Twice Int
lengthXtorArgs MkXtorArgs { prdArgs, cnsArgs } = Twice (length prdArgs) (length cnsArgs)

checkArgs :: Pretty a => Command a -> Twice [a] -> XtorArgs a -> EvalM ()
checkArgs cmd argTypes args =
  if fmap length argTypes == lengthXtorArgs args
  then return ()
  else throwEvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                        "\"\nArgument lengths don't coincide.")

-- | Returns Notihng if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalSTermOnce :: Command () -> EvalM (Maybe (Command ()))
evalSTermOnce Done = return Nothing
evalSTermOnce (Print _) = return Nothing
evalSTermOnce (Apply prd cns) = evalApplyOnce prd cns

evalApplyOnce :: STerm Prd () -> STerm Cns () -> EvalM (Maybe (Command ()))
-- Free variables have to be looked up in the environment.
evalApplyOnce (FreeVar PrdRep fv _) cns = do
  (prd,_) <- lookupPrd fv
  return (Just (Apply prd cns))
evalApplyOnce prd (FreeVar CnsRep fv _) = do
  (cns,_) <- lookupCns fv
  return (Just (Apply prd cns))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce prd@(XtorCall PrdRep xt args) cns@(XMatch CnsRep _ cases) = do
  (MkSCase _ argTypes cmd') <- lookupCase xt cases
  checkArgs (Apply prd cns) argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalApplyOnce prd@(XMatch PrdRep _ cases) cns@(XtorCall CnsRep xt args) = do
  (MkSCase _ argTypes cmd') <- lookupCase xt cases
  checkArgs (Apply prd cns) argTypes args
  return (Just (commandOpening args cmd')) --reduction is just opening
-- Mu abstractions have to be evaluated while taking care of evaluation order.
evalApplyOnce prd@(MuAbs PrdRep _ cmd) cns@(MuAbs CnsRep _ cmd') = do
  order <- lookupEvalOrder
  case order of
    CBV -> return (Just (commandOpeningSingle CnsRep cns cmd))
    CBN -> return (Just (commandOpeningSingle PrdRep prd cmd'))
evalApplyOnce (MuAbs PrdRep _ cmd) cns = return (Just (commandOpeningSingle CnsRep cns cmd))
evalApplyOnce prd (MuAbs CnsRep _ cmd) = return (Just (commandOpeningSingle PrdRep prd cmd))
-- Bound variables should not occur at the toplevel during evaluation.
evalApplyOnce (BoundVar PrdRep i) _ = throwEvalError $ "Found bound variable during evaluation. Index: " ++ show i
evalApplyOnce _ (BoundVar CnsRep i) = throwEvalError $ "Found bound variable during evaluation. Index: " ++ show i
-- Match applied to Match, or Xtor to Xtor can't evaluate
evalApplyOnce (XMatch _ _ _) (XMatch _ _ _) = throwEvalError "Cannot evaluate match applied to match"
evalApplyOnce (XtorCall _ _ _) (XtorCall _ _ _) = throwEvalError "Cannot evaluate constructor applied to destructor"

-- | Return just thef final evaluation result
eval :: Command () -> EvalM (Command ())
eval cmd = do
  cmd' <- evalSTermOnce cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> eval cmd'

-- | Return all intermediate evaluation results
evalSteps :: Command () -> EvalM [Command ()]
evalSteps cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: [Command ()] -> Command () -> EvalM [Command ()]
    evalSteps' cmds cmd = do
      cmd' <- evalSTermOnce cmd
      case cmd' of
        Nothing -> return cmds
        Just cmd' -> evalSteps' (cmds ++ [cmd']) cmd'
