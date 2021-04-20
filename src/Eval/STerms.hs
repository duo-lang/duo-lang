module Eval.STerms
  ( eval
  , evalSteps
  ) where

import Data.List (find)

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
  Nothing -> throwEvalError $ unlines ["Error during evaluation. The xtor: "
                                      , unXtorName xt
                                      , "doesn't occur in match."
                                      ]

lengthXtorArgs :: XtorArgs () FreeVarName -> Twice Int
lengthXtorArgs MkXtorArgs { prdArgs, cnsArgs } = Twice (length prdArgs) (length cnsArgs)

checkArgs :: Command () FreeVarName -> Twice [FreeVarName] -> XtorArgs () FreeVarName -> EvalM FreeVarName ()
checkArgs cmd argTypes args =
  if fmap length argTypes == lengthXtorArgs args
  then return ()
  else throwEvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                        "\"\nArgument lengths don't coincide.")

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
-- Pattern match depend on wether all arguments can be subst. into the Pattern.
evalApplyOnce prd@(XtorCall _ PrdRep _ args) cns@(XMatch _ CnsRep _ _) = do
  areSubst <- areAllSubst args
  case areSubst of
    True  -> substArgs prd cns
    False -> focusingStep prd cns
  where
    -- Subst all arguments of Ctor into corresponding pattern.
    substArgs :: STerm Prd () FreeVarName -> STerm Cns () FreeVarName -> EvalM FreeVarName (Maybe (Command () FreeVarName))
    substArgs prd@(XtorCall _ PrdRep xt args) cns@(XMatch _ CnsRep _ cases) = do
      (MkSCase _ argTypes cmd') <- lookupCase xt cases
      checkArgs (Apply () prd cns) argTypes args
      return (Just (commandOpening args cmd')) -- reduction is just opening
    substArgs _ _ = error "unrechable cases due to local definition of substArgs"
    -- Focus on first non-subst. argument and evaluate this from here onwards.
    focusingStep :: STerm Prd () FreeVarName -> STerm Cns () FreeVarName -> EvalM FreeVarName (Maybe (Command () FreeVarName))
    focusingStep (XtorCall ext PrdRep xt args) cns = 
      return $ Just $ Apply ext (getMu args) (MuAbs ext CnsRep "r" (Apply ext (XtorCall ext PrdRep xt (replaceMu args)) cns))
    focusingStep _ _ = error "unrechable cases due to local definition of focusingStep"

-- Copattern matches.
evalApplyOnce prd@(XMatch _ PrdRep _ _) cns@(XtorCall _ CnsRep _ args) = do
  areSubst <- areAllSubst args
  case areSubst of
    True  -> substArgs prd cns
    False -> focusingStep prd cns
  where
    -- Subst all arguments of Dtor into corresponding pattern.
    substArgs :: STerm Prd () FreeVarName -> STerm Cns () FreeVarName -> EvalM FreeVarName (Maybe (Command () FreeVarName))
    substArgs prd@(XMatch _ PrdRep _ cases) cns@(XtorCall _ CnsRep xt args) = do
      (MkSCase _ argTypes cmd') <- lookupCase xt cases
      checkArgs (Apply () prd cns) argTypes args
      return (Just (commandOpening args cmd')) -- reduction is just opening
    substArgs _ _ = error "unrechable cases due to local definition of substArgs"
    -- Focus on first non-subst. argument and evaluate this from here onwards.
    focusingStep :: STerm Prd () FreeVarName -> STerm Cns () FreeVarName -> EvalM FreeVarName (Maybe (Command () FreeVarName))
    focusingStep prd (XtorCall ext CnsRep xt args) =
      return $ Just $ Apply ext (getMu args) (MuAbs ext CnsRep "r" $ Apply ext prd (XtorCall ext CnsRep xt (replaceMu args)))
    focusingStep _ _ = error "unrechable cases due to local definition of focusingStep"

-- Mu abstractions have to be evaluated while taking care of evaluation order.
evalApplyOnce prd@(MuAbs _ PrdRep _ cmd) cns@(MuAbs _ CnsRep _ cmd') = do
  order <- lookupEvalOrder
  case order of
    CBV -> return (Just (commandOpeningSingle CnsRep cns cmd))
    CBN -> return (Just (commandOpeningSingle PrdRep prd cmd'))
evalApplyOnce (MuAbs _ PrdRep _ cmd) cns = return (Just (commandOpeningSingle CnsRep cns cmd))
evalApplyOnce prd (MuAbs _ CnsRep _ cmd) = return (Just (commandOpeningSingle PrdRep prd cmd))
-- Bound variables should not occur at the toplevel during evaluation.
evalApplyOnce (BoundVar _ PrdRep i) _ = throwEvalError $ "Found bound variable during evaluation. Index: " ++ show i
evalApplyOnce _ (BoundVar _ CnsRep i) = throwEvalError $ "Found bound variable during evaluation. Index: " ++ show i
-- Match applied to Match, or Xtor to Xtor can't evaluate
evalApplyOnce (XMatch _ _ _ _) (XMatch _ _ _ _) = throwEvalError "Cannot evaluate match applied to match"
evalApplyOnce (XtorCall _ _ _ _) (XtorCall _ _ _ _) = throwEvalError "Cannot evaluate constructor applied to destructor"

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


-- | Helper functions for CBV evaluation of match and comatch

-- | Replace currently evaluated MuAbs-argument in Xtor with bound variable
replaceMu :: XtorArgs ext FreeVarName -> XtorArgs ext FreeVarName
replaceMu MkXtorArgs { prdArgs, cnsArgs } = MkXtorArgs (replaceMuPrd prdArgs) cnsArgs
  where
    replaceMuPrd :: [STerm pc ext FreeVarName] -> [STerm pc ext FreeVarName] 
    replaceMuPrd (MuAbs ext PrdRep _ _ : prdArgs) = BoundVar ext PrdRep (0,0) : prdArgs
    replaceMuPrd (prd                  : prdArgs) = prd : replaceMuPrd prdArgs
    replaceMuPrd []                               = []

-- | Gets the first MuAbs-argrument from Xtor
getMu :: XtorArgs ext FreeVarName -> STerm Prd ext FreeVarName
getMu MkXtorArgs { prdArgs } = head $ filter isMu prdArgs

-- | Checks wether all producer arguments are substitutable.
-- | The evaluation order determines which arguments are substitutable.
areAllSubst :: XtorArgs ext FreeVarName -> EvalM FreeVarName Bool
areAllSubst MkXtorArgs { prdArgs } = do
  order <- lookupEvalOrder
  return $ all (isSubst order) prdArgs
  where
    isSubst :: EvalOrder -> STerm pc ext FreeVarName -> Bool
    isSubst CBV t = not $ isMu t -- subst every argument, unequal to Mu abstractions
    isSubst CBN _ = True         -- subst every argument

isMu :: STerm pc ext FreeVarName -> Bool
isMu (MuAbs _ PrdRep _ _) = True
isMu _                    = False
