module Eval.STerms
  ( eval
  , evalSteps
  ) where

import Data.List (find)
import Data.Text qualified as T

import Eval.Eval
    ( throwEvalError, EvalM )
import Lookup ( lookupSTerm )
import Pretty.Pretty ( ppPrint )
import Pretty.STerms ()
import Syntax.STerms
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

lengthXtorArgs :: XtorArgs Compiled -> Twice Int
lengthXtorArgs MkXtorArgs { prdArgs, cnsArgs } = Twice (length prdArgs) (length cnsArgs)

checkArgs :: Command Compiled -> Twice [a] -> XtorArgs Compiled -> EvalM ()
checkArgs cmd argTypes args =
  if fmap length argTypes == lengthXtorArgs args
  then return ()
  else throwEvalError [ "Error during evaluation of:"
                      , ppPrint cmd
                      , "Argument lengths don't coincide."
                      ]

-- | Returns Notihng if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalSTermOnce :: Command Compiled -> EvalM (Maybe (Command Compiled))
evalSTermOnce (Done _)                               = return Nothing
evalSTermOnce (Print _ _)                            = return Nothing
evalSTermOnce (Apply _ Nothing   _   _  )            = throwEvalError ["Found Apply command without kind annotation"]
evalSTermOnce (Apply _ (Just (KindVar _)) _ _)       = throwEvalError ["Found Apply command with kind variable annotation"]
evalSTermOnce (Apply _ (Just (MonoKind cc)) prd cns) = evalApplyOnce cc prd cns

evalApplyOnce :: CallingConvention -> STerm Prd Compiled -> STerm Cns Compiled -> EvalM  (Maybe (Command Compiled))
-- Free variables have to be looked up in the environment.
evalApplyOnce _ (FreeVar _ PrdRep fv) cns = do
  (prd,_) <- lookupSTerm PrdRep fv
  return (Just (Apply () Nothing (compileSTerm prd) cns))
evalApplyOnce _ prd (FreeVar _ CnsRep fv) = do
  (cns,_) <- lookupSTerm CnsRep fv
  return (Just (Apply () Nothing prd (compileSTerm cns)))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce _ prd@(XtorCall _ PrdRep xt args) cns@(XMatch _ CnsRep _ cases) = do
  (MkSCase _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply () Nothing prd cns) argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalApplyOnce _ prd@(XMatch _ PrdRep _ cases) cns@(XtorCall _ CnsRep xt args) = do
  (MkSCase _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply () Nothing prd cns) argTypes args
  return (Just (commandOpening args cmd')) --reduction is just opening
-- Mu abstractions have to be evaluated while taking care of evaluation order.
evalApplyOnce CBV     (MuAbs _ PrdRep _ cmd) cns@(MuAbs _ CnsRep _ _  ) = return (Just (commandOpeningSingle CnsRep cns cmd))
evalApplyOnce CBN prd@(MuAbs _ PrdRep _ _  )     (MuAbs _ CnsRep _ cmd) = return (Just (commandOpeningSingle PrdRep prd cmd))
evalApplyOnce _ (MuAbs _ PrdRep _ cmd) cns = return (Just (commandOpeningSingle CnsRep cns cmd))
evalApplyOnce _ prd (MuAbs _ CnsRep _ cmd) = return (Just (commandOpeningSingle PrdRep prd cmd))
-- Bound variables should not occur at the toplevel during evaluation.
evalApplyOnce _ (BoundVar _ PrdRep i) _ = throwEvalError ["Found bound variable during evaluation. Index: " <> T.pack (show i)]
evalApplyOnce _ _ (BoundVar _ CnsRep i) = throwEvalError [ "Found bound variable during evaluation. Index: " <> T.pack (show i)]
-- Match applied to Match, or Xtor to Xtor can't evaluate
evalApplyOnce _ (XMatch _ _ _ _) (XMatch _ _ _ _) = throwEvalError ["Cannot evaluate match applied to match"]
evalApplyOnce _ (XtorCall _ _ _ _) (XtorCall _ _ _ _) = throwEvalError ["Cannot evaluate constructor applied to destructor"]



-- | Return just thef final evaluation result
eval :: Command Compiled -> EvalM (Command Compiled)
eval cmd = do
  cmd' <- evalSTermOnce cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> eval cmd'

-- | Return all intermediate evaluation results
evalSteps :: Command Compiled -> EvalM [Command Compiled]
evalSteps cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: [Command Compiled] -> Command Compiled -> EvalM [Command Compiled]
    evalSteps' cmds cmd = do
      cmd' <- evalSTermOnce cmd
      case cmd' of
        Nothing -> return cmds
        Just cmd' -> evalSteps' (cmds ++ [cmd']) cmd'

