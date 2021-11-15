module Eval.Terms
  ( eval
  , evalSteps
  ) where

import Data.List (find)
import Data.Text qualified as T

import Eval.Eval
    ( throwEvalError, lookupEvalOrder, EvalM )
import Lookup ( lookupSTerm )
import Pretty.Pretty ( ppPrint )
import Pretty.Terms ()
import Syntax.Terms
import Syntax.CommonTerm
import Syntax.Kinds
import Utils
import Translate.Translate

---------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------

lookupMatchCase :: XtorName -> [SCase Compiled] -> EvalM (SCase Compiled)
lookupMatchCase xt cases = case find (\MkSCase { scase_name } -> xt == scase_name) cases of
  Just pmcase -> return pmcase
  Nothing -> throwEvalError ["Error during evaluation. The xtor: "
                            , unXtorName xt
                            , "doesn't occur in match."
                            ]

lengthSubstitution :: Substitution Compiled -> Twice Int
lengthSubstitution subst = Twice (length prdArgs) (length cnsArgs)
  where
    (prdArgs, cnsArgs) = newToOldSubst subst

checkArgs :: Command Compiled -> Twice [a] -> Substitution Compiled -> EvalM ()
checkArgs cmd argTypes args =
  if fmap length argTypes == lengthSubstitution args
  then return ()
  else throwEvalError [ "Error during evaluation of:"
                      , ppPrint cmd
                      , "Argument lengths don't coincide."
                      ]

-- | Returns Notihng if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalTermOnce :: Command Compiled -> EvalM (Maybe (Command Compiled))
evalTermOnce (Done _) = return Nothing
evalTermOnce (Print _ _) = return Nothing
evalTermOnce (Apply _ prd cns) = evalApplyOnce prd cns

evalApplyOnce :: Term Prd Compiled -> Term Cns Compiled -> EvalM  (Maybe (Command Compiled))
-- Free variables have to be looked up in the environment.
evalApplyOnce (FreeVar _ PrdRep fv) cns = do
  (prd,_) <- lookupSTerm PrdRep fv
  return (Just (Apply () (compile prd) cns))
evalApplyOnce prd (FreeVar _ CnsRep fv) = do
  (cns,_) <- lookupSTerm CnsRep fv
  return (Just (Apply () prd (compile cns)))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce prd@(XtorCall _ PrdRep xt args) cns@(XMatch _ CnsRep _ cases) = do
  (MkSCase _ _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply () prd cns) argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalApplyOnce prd@(XMatch _ PrdRep _ cases) cns@(XtorCall _ CnsRep xt args) = do
  (MkSCase _ _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply () prd cns) argTypes args
  return (Just (commandOpening args cmd')) --reduction is just opening
-- Mu abstractions have to be evaluated while taking care of evaluation order.
evalApplyOnce prd@(MuAbs _ PrdRep _ cmd) cns@(MuAbs _ CnsRep _ cmd') = do
  order <- lookupEvalOrder
  case order of
    CBV -> return (Just (commandOpeningSingle CnsRep cns cmd))
    CBN -> return (Just (commandOpeningSingle PrdRep prd cmd'))
evalApplyOnce (MuAbs _ PrdRep _ cmd) cns = return (Just (commandOpeningSingle CnsRep cns cmd))
evalApplyOnce prd (MuAbs _ CnsRep _ cmd) = return (Just (commandOpeningSingle PrdRep prd cmd))
-- Bound variables should not occur at the toplevel during evaluation.
evalApplyOnce (BoundVar _ PrdRep i) _ = throwEvalError ["Found bound variable during evaluation. Index: " <> T.pack (show i)]
evalApplyOnce _ (BoundVar _ CnsRep i) = throwEvalError [ "Found bound variable during evaluation. Index: " <> T.pack (show i)]
-- Match applied to Match, or Xtor to Xtor can't evaluate
evalApplyOnce (XMatch _ _ _ _) (XMatch _ _ _ _) = throwEvalError ["Cannot evaluate match applied to match"]
evalApplyOnce (XtorCall _ _ _ _) (XtorCall _ _ _ _) = throwEvalError ["Cannot evaluate constructor applied to destructor"]


-- | Return just thef final evaluation result
eval :: Command Compiled -> EvalM (Command Compiled)
eval cmd = do
  cmd' <- evalTermOnce cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> eval cmd'

-- | Return all intermediate evaluation results
evalSteps :: Command Compiled -> EvalM [Command Compiled]
evalSteps cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: [Command Compiled] -> Command Compiled -> EvalM [Command Compiled]
    evalSteps' cmds cmd = do
      cmd' <- evalTermOnce cmd
      case cmd' of
        Nothing -> return cmds
        Just cmd' -> evalSteps' (cmds ++ [cmd']) cmd'
