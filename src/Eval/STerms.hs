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

lookupCase :: XtorName -> [SCase () bs] -> EvalM bs (SCase () bs)
lookupCase xt cases = case find (\MkSCase { scase_name } -> xt == scase_name) cases of
  Just pmcase -> return pmcase
  Nothing -> throwEvalError $ unlines ["Error during evaluation. The xtor: "
                                      , unXtorName xt
                                      , "doesn't occur in match."
                                      ]

lengthXtorArgs :: XtorArgs () bs -> Twice Int
lengthXtorArgs MkXtorArgs { prdArgs, cnsArgs } = Twice (length prdArgs) (length cnsArgs)

checkArgs :: PrettyAnn bs => Command () bs -> Twice [bs] -> XtorArgs () bs -> EvalM bs ()
checkArgs cmd argTypes args =
  if fmap length argTypes == lengthXtorArgs args
  then return ()
  else throwEvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                        "\"\nArgument lengths don't coincide.")

-- | Returns Notihng if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalSTermOnce :: PrettyAnn bs => Command () bs -> EvalM bs (Maybe (Command () bs))
evalSTermOnce (Done _) = return Nothing
evalSTermOnce (Print _ _) = return Nothing
evalSTermOnce (Apply _ prd cns) = evalApplyOnce prd cns

evalApplyOnce :: PrettyAnn bs => STerm Prd () bs -> STerm Cns () bs -> EvalM bs (Maybe (Command () bs))
-- Free variables have to be looked up in the environment.
evalApplyOnce (FreeVar _ PrdRep fv) cns = do
  (prd,_) <- lookupPrd fv
  return (Just (Apply () prd cns))
evalApplyOnce prd (FreeVar _ CnsRep fv) = do
  (cns,_) <- lookupCns fv
  return (Just (Apply () prd cns))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce prd@(XtorCall _ PrdRep xt args) cns@(XMatch _ CnsRep _ cases) = do
  order <- lookupEvalOrder
  evalMatchOnce prd cns order
  where
    evalMatchOnce :: PrettyAnn bs => STerm Prd () bs -> STerm Cns () bs -> EvalOrder -> EvalM bs (Maybe (Command () bs))
    evalMatchOnce prd@(XtorCall _ PrdRep xt args) cns@(XMatch _ CnsRep _ cases) CBN = do
      (MkSCase _ argTypes cmd') <- lookupCase xt cases
      checkArgs (Apply () prd cns) argTypes args
      return (Just (commandOpening args cmd')) --reduction is just opening

    evalMatchOnce prd@(XtorCall ext PrdRep xt args) cns CBV | noMu args = evalMatchOnce prd cns CBN
                                                            | otherwise = -- focusing step                                 ???
                                                                 return (Just (Apply ext (getMuAbs args) (MuAbs ext CnsRep "r" (Apply ext (XtorCall ext PrdRep xt (replaceMu args)) cns))))

evalApplyOnce prd@(XMatch _ PrdRep _ cases) cns@(XtorCall _ CnsRep xt args) = do
  order <- lookupEvalOrder
  evalComatchOnce prd cns order
  where
    evalComatchOnce :: PrettyAnn bs => STerm Prd () bs -> STerm Cns () bs -> EvalOrder -> EvalM bs (Maybe (Command () bs))
    evalComatchOnce prd@(XMatch _ PrdRep _ cases) cns@(XtorCall _ CnsRep xt args) CBN = do
      (MkSCase _ argTypes cmd') <- lookupCase xt cases
      checkArgs (Apply () prd cns) argTypes args
      return (Just (commandOpening args cmd')) --reduction is just opening

    evalComatchOnce prd cns@(XtorCall ext CnsRep xt args) CBV | noMu args = evalComatchOnce prd cns CBN
                                                              | otherwise = -- focusing step                                   ???
                                                                  return $ Just $ Apply ext (getMuAbs args) $ MuAbs ext CnsRep "r" $ Apply ext prd (XtorCall ext CnsRep xt (replaceMu args))
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
eval :: PrettyAnn bs => Command () bs -> EvalM bs (Command () bs)
eval cmd = do
  cmd' <- evalSTermOnce cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> eval cmd'

-- | Return all intermediate evaluation results
evalSteps :: PrettyAnn bs => Command () bs -> EvalM bs [Command () bs]
evalSteps cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: PrettyAnn bs => [Command () bs] -> Command () bs -> EvalM bs [Command () bs]
    evalSteps' cmds cmd = do
      cmd' <- evalSTermOnce cmd
      case cmd' of
        Nothing -> return cmds
        Just cmd' -> evalSteps' (cmds ++ [cmd']) cmd'


-- | helper functions for CBV evaluation of match and comatch

-- | replace currently evaluated argument in Xtor
replaceMu :: XtorArgs ext bs -> XtorArgs ext bs
replaceMu MkXtorArgs { prdArgs, cnsArgs } = MkXtorArgs (replaceMuPrd prdArgs) cnsArgs
--  where
replaceMuPrd :: [STerm pc ext bs] -> [STerm pc ext bs] 
replaceMuPrd (MuAbs ext PrdRep _ _ : prdArgs) = BoundVar ext PrdRep (0,0) : prdArgs
replaceMuPrd ( prd : prdArgs)                 = prd : replaceMuPrd prdArgs

-- | gets MuAbs-argrument from Xtor
getMuAbs :: XtorArgs ext bs -> STerm Prd ext bs
getMuAbs MkXtorArgs { prdArgs } = head $ filter isMu prdArgs

-- | checks if no arguments is a MuAbs
noMu :: XtorArgs ext bs -> Bool
noMu MkXtorArgs { prdArgs } = all (not . isMu) prdArgs

isMu :: STerm pc ext bs -> Bool
isMu (MuAbs _ PrdRep _ _) = True
isMu _                    = False
