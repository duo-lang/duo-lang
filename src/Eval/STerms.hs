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

checkArgs :: PrettyAnn FreeVarName => Command () FreeVarName -> Twice [FreeVarName] -> XtorArgs () FreeVarName -> EvalM FreeVarName ()
checkArgs cmd argTypes args =
  if fmap length argTypes == lengthXtorArgs args
  then return ()
  else throwEvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                        "\"\nArgument lengths don't coincide.")

-- | Returns Notihng if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalSTermOnce :: PrettyAnn FreeVarName => Command () FreeVarName -> EvalM FreeVarName (Maybe (Command () FreeVarName))
evalSTermOnce (Done _) = return Nothing
evalSTermOnce (Print _ _) = return Nothing
evalSTermOnce (Apply _ prd cns) = evalApplyOnce prd cns

evalApplyOnce :: PrettyAnn FreeVarName => STerm Prd () FreeVarName -> STerm Cns () FreeVarName -> EvalM FreeVarName (Maybe (Command () FreeVarName))
-- Free variables have to be looked up in the environment.
evalApplyOnce (FreeVar _ PrdRep fv) cns = do
  (prd,_) <- lookupPrd fv
  return (Just (Apply () prd cns))
evalApplyOnce prd (FreeVar _ CnsRep fv) = do
  (cns,_) <- lookupCns fv
  return (Just (Apply () prd cns))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce prd@(XtorCall _ PrdRep _ _) cns@(XMatch _ CnsRep _ _) = do
  order <- lookupEvalOrder
  evalMatchOnce prd cns order
  where
    evalMatchOnce :: PrettyAnn FreeVarName => STerm Prd () FreeVarName -> STerm Cns () FreeVarName -> EvalOrder -> EvalM FreeVarName (Maybe (Command () FreeVarName))
    --evalMatchOnce :: PrettyAnn FreeVarName => STerm Prd () FreeVarName -> STerm Cns () FreeVarName -> EvalOrder -> EvalM FreeVarName (Maybe (Command () FreeVarName))
    evalMatchOnce prd@(XtorCall _ PrdRep xt args) cns@(XMatch _ CnsRep _ cases) CBN = do
      (MkSCase _ argTypes cmd') <- lookupCase xt cases
      checkArgs (Apply () prd cns) argTypes args
      return (Just (commandOpening args cmd')) --reduction is just opening

    evalMatchOnce prd@(XtorCall ext PrdRep xt args) cns CBV | noMu args = evalMatchOnce prd cns CBN
                                                            | otherwise = -- focusing step                                 ???
                                                                 return (Just (Apply ext (getMuAbs args) (MuAbs ext CnsRep "r" (Apply ext (XtorCall ext PrdRep xt (replaceMu args)) cns))))
    evalMatchOnce _ _ _ = error "unreachable error"

evalApplyOnce prd@(XMatch _ PrdRep _ _) cns@(XtorCall _ CnsRep _ _) = do
  order <- lookupEvalOrder
  evalComatchOnce prd cns order
  where
    evalComatchOnce :: PrettyAnn FreeVarName => STerm Prd () FreeVarName -> STerm Cns () FreeVarName -> EvalOrder -> EvalM FreeVarName (Maybe (Command () FreeVarName))
    evalComatchOnce prd@(XMatch _ PrdRep _ cases) cns@(XtorCall _ CnsRep xt args) CBN = do
      (MkSCase _ argTypes cmd') <- lookupCase xt cases
      checkArgs (Apply () prd cns) argTypes args
      return (Just (commandOpening args cmd')) --reduction is just opening

    evalComatchOnce prd cns@(XtorCall ext CnsRep xt args) CBV | noMu args = evalComatchOnce prd cns CBN
                                                              | otherwise = -- focusing step                                   ???
                                                                  return $ Just $ Apply ext (getMuAbs args) $ MuAbs ext CnsRep "r" $ Apply ext prd (XtorCall ext CnsRep xt (replaceMu args))
    evalComatchOnce _ _ _ = error "unreachable error"

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
eval :: PrettyAnn FreeVarName => Command () FreeVarName -> EvalM FreeVarName (Command () FreeVarName)
eval cmd = do
  cmd' <- evalSTermOnce cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> eval cmd'

-- | Return all intermediate evaluation results
evalSteps :: PrettyAnn FreeVarName => Command () FreeVarName -> EvalM FreeVarName [Command () FreeVarName]
evalSteps cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: PrettyAnn FreeVarName => [Command () FreeVarName] -> Command () FreeVarName -> EvalM FreeVarName [Command () FreeVarName]
    evalSteps' cmds cmd = do
      cmd' <- evalSTermOnce cmd
      case cmd' of
        Nothing -> return cmds
        Just cmd' -> evalSteps' (cmds ++ [cmd']) cmd'


-- | helper functions for CBV evaluation of match and comatch

-- | replace currently evaluated argument in Xtor
replaceMu :: XtorArgs ext FreeVarName -> XtorArgs ext FreeVarName
replaceMu MkXtorArgs { prdArgs, cnsArgs } = MkXtorArgs (replaceMuPrd prdArgs) cnsArgs
--  where
replaceMuPrd :: [STerm pc ext FreeVarName] -> [STerm pc ext FreeVarName] 
replaceMuPrd (MuAbs ext PrdRep _ _ : prdArgs) = BoundVar ext PrdRep (0,0) : prdArgs
replaceMuPrd (prd                  : prdArgs) = prd : replaceMuPrd prdArgs
replaceMuPrd []                               = []

-- | gets MuAbs-argrument from Xtor
getMuAbs :: XtorArgs ext FreeVarName -> STerm Prd ext FreeVarName
getMuAbs MkXtorArgs { prdArgs } = head $ filter isMu prdArgs

-- | checks if no arguments is a MuAbs
noMu :: XtorArgs ext FreeVarName -> Bool
noMu MkXtorArgs { prdArgs } = all (not . isMu) prdArgs

isMu :: STerm pc ext FreeVarName -> Bool
isMu (MuAbs _ PrdRep _ _) = True
isMu _                    = False
