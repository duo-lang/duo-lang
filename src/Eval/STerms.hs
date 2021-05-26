module Eval.STerms
  ( eval
  , evalSteps
  , areAllSubst
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
evalApplyOnce (BoundVar _ PrdRep i) _ = throwEvalError $ "Found bound variable during evaluation. Index: " ++ show i
evalApplyOnce _ (BoundVar _ CnsRep i) = throwEvalError $ "Found bound variable during evaluation. Index: " ++ show i
-- Match applied to Match, or Xtor to Xtor can't evaluate
evalApplyOnce (XMatch _ _ _ _) (XMatch _ _ _ _) = throwEvalError "Cannot evaluate match applied to match"
evalApplyOnce (XtorCall _ _ _ _) (XtorCall _ _ _ _) = throwEvalError "Cannot evaluate constructor applied to destructor"


-- | Returns Notihng if command doesn't need a focusing step, just cmd' if cmd changes to cmd' in one focusing step
focusOnce :: Command () FreeVarName -> EvalM FreeVarName (Maybe (Command () FreeVarName))
focusOnce (Done _) = return Nothing
focusOnce (Print _ _) = return Nothing
focusOnce (Apply _ prd cns) = focusApplyOnce prd cns

focusApplyOnce :: STerm Prd () FreeVarName -> STerm Cns () FreeVarName -> EvalM FreeVarName (Maybe (Command () FreeVarName))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
-- Pattern match depend on wether all arguments can be subst. into the Pattern.
focusApplyOnce prd@(XtorCall _ PrdRep _ args) cns@(XMatch _ CnsRep _ _) = do
  order <- lookupEvalOrder
  case areAllSubst order args of
    True  -> return Nothing
    False -> focusingStep prd cns
  where
    -- we want to focus on the first non-subst. argument
    -- at CBV in:  C(prds not-sub prds)[cnss] >> cns
    -- to:         not-sub >> mu r. C(prds r prds)[cnss] >> cns
    -- at CBN in:  C(prds)[cnss not-sub cnss] >> cns
    -- to:         mu r. C(prds)[cnss r cnss] >> not-sub
    focusingStep :: STerm Prd () FreeVarName -> STerm Cns () FreeVarName -> EvalM FreeVarName (Maybe (Command () FreeVarName))
    focusingStep (XtorCall ext PrdRep xt args) cns =  do
      order <- lookupEvalOrder
      case replaceMu order args of
        (args', (muP, muC)) ->
          case order of
            CBV -> return $ Just $ Apply ext (head muP) (MuAbs ext CnsRep "r" (Apply ext (XtorCall ext PrdRep xt args') cns))
            CBN -> return $ Just $ Apply ext (MuAbs ext PrdRep "r" (Apply ext (XtorCall ext PrdRep xt args') cns)) (head muC)
    focusingStep _ _ = error "unrechable cases due to local definition of focusingStep"
-- Copattern matches.
focusApplyOnce prd@(XMatch _ PrdRep _ _) cns@(XtorCall _ CnsRep _ args) = do
  order <- lookupEvalOrder
  case areAllSubst order args of
    True  -> return Nothing
    False -> focusingStep prd cns
  where
    -- we want to focus on the first non-subst. argument
    -- at CBV in:  prd >> D(prds not-sub prds)[cnss]
    -- to:         not-sub >> mu r. prd >> D(prds r prds)[cnss]
    -- at CBN in:  prd >> D(prds)[cnss not-sub cnss]
    -- to:         mu r.prd >> D(prds)[cnss r cnss] >> not-sub
    focusingStep :: STerm Prd () FreeVarName -> STerm Cns () FreeVarName -> EvalM FreeVarName (Maybe (Command () FreeVarName))
    focusingStep prd (XtorCall ext CnsRep xt args) = do
      order <- lookupEvalOrder
      case replaceMu order args of
        (args', (muP, muC)) ->
          case order of
            CBV -> return $ Just $ Apply ext (head muP) (MuAbs ext CnsRep "r" $ Apply ext prd (XtorCall ext CnsRep xt args'))
            CBN -> return $ Just $ Apply ext (MuAbs ext PrdRep "r" $ Apply ext prd (XtorCall ext CnsRep xt args')) (head muC)
    focusingStep _ _ = error "unrechable cases due to local definition of focusingStep"
-- all other cases don't need focusing steps
focusApplyOnce _ _ = return Nothing


-- | Return just thef final evaluation result
eval :: Command () FreeVarName -> EvalM FreeVarName (Command () FreeVarName)
eval cmd = do
  focusedCmd <- focusOnce cmd
  case focusedCmd of
    Nothing -> do
      cmd' <- evalSTermOnce cmd
      case cmd' of
        Nothing -> return cmd
        Just cmd' -> eval cmd'
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
replaceMu :: EvalOrder -> XtorArgs () FreeVarName -> (XtorArgs () FreeVarName, ([STerm Prd () FreeVarName], [STerm Cns () FreeVarName]))
replaceMu order args = replaceMuAcc order args
  where
    replaceMuAcc :: EvalOrder -> XtorArgs () FreeVarName -> (XtorArgs () FreeVarName, ([STerm Prd () FreeVarName], [STerm Cns () FreeVarName]))
    replaceMuAcc order MkXtorArgs { prdArgs, cnsArgs }| not (all (isSubstPrd order) prdArgs) = 
                                                          case replaceMuPrd order prdArgs of 
                                                            (prds, mu) -> (MkXtorArgs prds cnsArgs, mu)
                                                      | otherwise =  
                                                          case replaceMuCns order cnsArgs of 
                                                            (cnss, mu) -> (MkXtorArgs prdArgs cnss, mu)

    replaceMuPrd :: EvalOrder -> [STerm Prd () FreeVarName] -> ([STerm Prd () FreeVarName], ([STerm Prd () FreeVarName], [STerm Cns () FreeVarName]))
    replaceMuPrd CBV   (mu@(MuAbs ext _ _ _) : prdArgs) = ((BoundVar ext PrdRep (0,0) : prdArgs), ([mu],[]))
    replaceMuPrd order (xtor@(XtorCall ext PrdRep xt args@(MkXtorArgs { prdArgs, cnsArgs })) : ts) | areAllSubst order args =
                                                                                                       case replaceMuPrd order ts of 
                                                                                                         (prds, mu) -> ((xtor : prds), mu)
                                                                                                   | not (all (isSubstPrd order) prdArgs) = 
                                                                                                       case replaceMuPrd order prdArgs of
                                                                                                         (prds, mu) -> (((XtorCall ext PrdRep xt (MkXtorArgs prds cnsArgs)) : ts) , mu)
                                                                                                   | otherwise = 
                                                                                                       case replaceMuCns order cnsArgs of
                                                                                                         (cnss, mu) -> (((XtorCall ext PrdRep xt (MkXtorArgs prdArgs cnss)) : ts), mu)
    replaceMuPrd order (prd : prdArgs) | isSubstPrd order prd = 
                                           case replaceMuPrd order prdArgs of
                                             (prds, mu) -> ((prd : prds), mu)
                                       | otherwise = error $ (show prd) ++ "isn't subsitutable, but should have been!"
    replaceMuPrd _ [] = error "Couldn't find and replace a (tilde) mu abstraction, but should have!"

    replaceMuCns :: EvalOrder -> [STerm Cns () FreeVarName] ->  ([STerm Cns () FreeVarName],  ([STerm Prd () FreeVarName], [STerm Cns () FreeVarName]))
    replaceMuCns CBN   (mu@(MuAbs ext _ _ _) : cnsArgs) = ((BoundVar ext CnsRep (0,0) : cnsArgs), ([],[mu]))
    replaceMuCns order (xtor@(XtorCall ext CnsRep xt args@(MkXtorArgs { prdArgs, cnsArgs })) : ts) | areAllSubst order args = 
                                                                                                       case replaceMuCns order ts of 
                                                                                                         (cnss, mu) -> ((xtor : cnss), mu)
                                                                                                   | not (all (isSubstPrd order) prdArgs) = 
                                                                                                       case replaceMuPrd order prdArgs of
                                                                                                         (prds, mu) -> (((XtorCall ext CnsRep xt (MkXtorArgs prds cnsArgs)) : ts), mu)
                                                                                                   | otherwise = 
                                                                                                       case replaceMuCns order cnsArgs of
                                                                                                         (cnss, mu) -> (((XtorCall ext CnsRep xt (MkXtorArgs prdArgs cnss)) : ts), mu)
    replaceMuCns order (cns : cnsArgs) | isSubstCns order cns =
                                           case replaceMuCns order cnsArgs of
                                             (cnss, mu) -> ((cns : cnss), mu)
                                       | otherwise = error $ (show cns) ++ "isn't subsitutable, but should have been!"
    replaceMuCns _     [] = error "Couldn't find and replace a (tilde) mu abstraction, but should have!"

-- | Checks wether all producer arguments are substitutable.
-- | The evaluation order determines which arguments are substitutable.
areAllSubst :: EvalOrder -> XtorArgs ext FreeVarName -> Bool
areAllSubst order (MkXtorArgs { prdArgs, cnsArgs }) =
  all (isSubstPrd order) prdArgs && all (isSubstCns order) cnsArgs

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
