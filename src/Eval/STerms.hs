module Eval.STerms
  ( eval
  , evalSteps
  , areAllSubst
  ) where

import Data.List (find)
import qualified Data.Text as T

import Eval.Eval
import Pretty.Pretty
import Pretty.STerms ()
import Syntax.STerms
import Utils

---------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------

lookupCase :: XtorName -> [SCase () FreeVarName] -> EvalM FreeVarName (SCase () FreeVarName)
lookupCase xt cases = case find (\MkSCase { scase_name } -> xt == scase_name) cases of
  Just pmcase -> return pmcase
  Nothing -> throwEvalError ["Error during evaluation. The xtor: "
                            , unXtorName xt
                            , "doesn't occur in match."
                            ]

lengthXtorArgs :: XtorArgs () FreeVarName -> Twice Int
lengthXtorArgs MkXtorArgs { prdArgs, cnsArgs } = Twice (length prdArgs) (length cnsArgs)

checkArgs :: Command () FreeVarName -> Twice [FreeVarName] -> XtorArgs () FreeVarName -> EvalM FreeVarName ()
checkArgs cmd argTypes args =
  if fmap length argTypes == lengthXtorArgs args
  then return ()
  else throwEvalError [ "Error during evaluation of:"
                      , ppPrint cmd
                      , "Argument lengths don't coincide."
                      ]

-- | Returns Notihng if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalSTermOnce :: Command () FreeVarName -> EvalM FreeVarName (Maybe (Command () FreeVarName))
evalSTermOnce (Done _) = return Nothing
evalSTermOnce (Print _ _) = return Nothing
evalSTermOnce (Apply _ prd cns) = evalApplyOnce prd cns

evalApplyOnce :: STerm Prd () FreeVarName -> STerm Cns () FreeVarName -> EvalM FreeVarName (Maybe (Command () FreeVarName))
-- Free variables have to be looked up in the environment.
evalApplyOnce (FreeVar _ PrdRep fv) cns = do
  (prd,_) <- lookupPrd fv
  return (Just (Apply () prd cns))
evalApplyOnce prd (FreeVar _ CnsRep fv) = do
  (cns,_) <- lookupCns fv
  return (Just (Apply () prd cns))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce prd@(XtorCall _ PrdRep xt args) cns@(XMatch _ CnsRep _ cases) = do
  (MkSCase _ argTypes cmd') <- lookupCase xt cases
  checkArgs (Apply () prd cns) argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalApplyOnce prd@(XMatch _ PrdRep _ cases) cns@(XtorCall _ CnsRep xt args) = do
  (MkSCase _ argTypes cmd') <- lookupCase xt cases
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
eval :: Command () FreeVarName -> EvalM FreeVarName (Command () FreeVarName)
eval cmd = do
  cmd' <- evalSTermOnce cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> eval cmd'

-- | Return all intermediate evaluation results
evalSteps :: Command () FreeVarName -> EvalM FreeVarName [Command () FreeVarName]
evalSteps cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: [Command () FreeVarName] -> Command () FreeVarName -> EvalM FreeVarName [Command () FreeVarName]
    evalSteps' cmds cmd = do
      cmd' <- evalSTermOnce cmd
      case cmd' of
        Nothing -> return cmds
        Just cmd' -> evalSteps' (cmds ++ [cmd']) cmd'



-- | Checks wether all producer arguments are substitutable.
-- | The evaluation order determines which arguments are substitutable.
areAllSubst :: EvalOrder -> XtorArgs ext FreeVarName -> Bool
areAllSubst order (MkXtorArgs { prdArgs, cnsArgs }) = all (isSubstPrd order) prdArgs && all (isSubstCns order) cnsArgs

-- subst every producer argument, not containing any mu-abstractions
isSubstPrd :: EvalOrder -> STerm Prd ext FreeVarName -> Bool
isSubstPrd _   (BoundVar _ _ _) = True
isSubstPrd _   (FreeVar _ _ _)  = True
isSubstPrd ord (XtorCall _ _ _ args) = areAllSubst ord args
isSubstPrd _   (XMatch _ _ _ _) = True
isSubstPrd CBV (MuAbs _ _ _ _)  = False
isSubstPrd CBN (MuAbs _ _ _ _)  = True

-- subst every producer argument, not containing any ~mu-abstractions
isSubstCns :: EvalOrder -> STerm Cns ext FreeVarName -> Bool
isSubstCns _   (BoundVar _ _ _) = True
isSubstCns _   (FreeVar _ _ _)  = True
isSubstCns ord (XtorCall _ _ _ args) = areAllSubst ord args
isSubstCns _   (XMatch _ _ _ _) = True
isSubstCns CBV (MuAbs _ _ _ _)  = True
isSubstCns CBN (MuAbs _ _ _ _)  = False
