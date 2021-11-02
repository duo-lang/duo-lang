module Eval.STerms
  ( eval
  , evalSteps
  , areAllSubst
  ) where

import Data.List (find)
import qualified Data.Text as T

import Eval.Eval
    ( throwEvalError, lookupEvalOrder, EvalM )
import Lookup ( lookupSTerm )
import Pretty.Pretty ( ppPrint )
import Pretty.STerms ()
import Syntax.STerms
import Syntax.Kinds ( CallingConvention(CBN, CBV) )
import Utils ( Twice(..) )
import Utils
import Translate.Translate
import Syntax.ATerms


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
evalSTermOnce (Done _) = return Nothing
evalSTermOnce (Print _ _) = return Nothing
evalSTermOnce (Apply _ _ prd cns) = evalApplyOnce prd cns

evalApplyOnce :: STerm Prd Compiled -> STerm Cns Compiled -> EvalM  (Maybe (Command Compiled))
-- Free variables have to be looked up in the environment.
evalApplyOnce (FreeVar _ PrdRep fv) cns = do
  (prd,_) <- lookupSTerm PrdRep fv
  return (Just (Apply () Nothing (compileSTerm prd) cns))
evalApplyOnce prd (FreeVar _ CnsRep fv) = do
  (cns,_) <- lookupSTerm CnsRep fv
  return (Just (Apply () Nothing prd (compileSTerm cns)))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce prd@(XtorCall _ PrdRep xt args) cns@(XMatch _ CnsRep _ cases) = do
  (MkSCase _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply () Nothing prd cns) argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalApplyOnce prd@(XMatch _ PrdRep _ cases) cns@(XtorCall _ CnsRep xt args) = do
  (MkSCase _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply () Nothing prd cns) argTypes args
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


-- | Returns Notihng if command doesn't need a focusing step, just cmd' if cmd changes to cmd' in one focusing step
focusOnce :: Command Compiled -> EvalM (Maybe (Command Compiled))
focusOnce (Done _) = return Nothing
focusOnce (Print _ _) = return Nothing
focusOnce (Apply _ _ prd cns) = focusApplyOnce prd cns

focusApplyOnce :: STerm Prd Compiled -> STerm Cns Compiled -> EvalM (Maybe (Command Compiled))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
-- Pattern match depend on wether all arguments can be subst. into the Pattern.
focusApplyOnce prd@(XtorCall _ PrdRep _ args) cns@(XMatch _ CnsRep _ _) = do
  order <- lookupEvalOrder
  if areAllSubst order args
    then return Nothing
    else focusingStep prd cns
  where
    -- we want to focus on the first non-subst. argument
    -- at CBV in:  C(prds not-sub prds)[cnss] >> cns
    -- to:         not-sub >> mu r. C(prds r prds)[cnss] >> cns
    -- at CBN in:  C(prds)[cnss not-sub cnss] >> cns
    -- to:         mu r. C(prds)[cnss r cnss] >> not-sub
    focusingStep :: STerm Prd Compiled -> STerm Cns Compiled -> EvalM (Maybe (Command Compiled))
    focusingStep (XtorCall ext PrdRep xt args) cns =  do
      order <- lookupEvalOrder
      case replaceMu order args of
        (args', mu) ->
          let xc = XtorCall ext PrdRep xt args'
          in return $ Just $ case order of
                CBV -> Apply ext Nothing (fromLeft mu) (MuAbs ext CnsRep (Just "r") (Apply ext Nothing xc cns))
                CBN -> Apply ext Nothing (MuAbs ext PrdRep (Just "r") (Apply ext Nothing xc cns)) (fromRight mu)
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
    focusingStep :: STerm Prd Compiled -> STerm Cns Compiled -> EvalM (Maybe (Command Compiled))
    focusingStep prd (XtorCall ext CnsRep xt args) = do
      order <- lookupEvalOrder
      case replaceMu order args of
        (args', mu) ->
          let xc = XtorCall ext CnsRep xt args'
          in return $ Just $ case order of
            CBV -> Apply ext Nothing (fromLeft mu) (MuAbs ext CnsRep (Just "r") $ Apply ext Nothing prd xc)
            CBN -> Apply ext Nothing (MuAbs ext PrdRep (Just "r") $ Apply ext Nothing prd xc) (fromRight mu)
    focusingStep _ _ = error "unrechable cases due to local definition of focusingStep"
-- all other cases don't need focusing steps
focusApplyOnce _ _ = return Nothing


-- | Returns Notihng if command doesn't need a focusing or eval step, 
-- | just cmd' if cmd changes to cmd' in one focusing step 
-- | or cmd'' if cmd cahnges throough an eval step
evalOrFocusOnce :: Command Compiled -> EvalM (Maybe (Command Compiled))
evalOrFocusOnce cmd = do
  focusedCmd <- focusOnce cmd
  case focusedCmd of
    Nothing -> evalSTermOnce cmd
    Just cmd' -> return $ Just cmd'

-- | Return just thef final evaluation result
eval :: Command Compiled -> EvalM (Command Compiled)
eval cmd = do
  cmd' <- evalOrFocusOnce cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> eval cmd'

-- | Return all intermediate evaluation results
evalSteps :: Command Compiled -> EvalM [Command Compiled]
evalSteps cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: [Command Compiled] -> Command Compiled -> EvalM [Command Compiled]
    evalSteps' cmds cmd = do
      cmd' <- evalOrFocusOnce cmd
      case cmd' of
        Nothing -> return cmds
        Just cmd' -> evalSteps' (cmds ++ [cmd']) cmd'

-- | Helper functions for CBV evaluation of match and comatch
    
-- | Replace currently evaluated MuAbs-argument in Xtor with bound variable and give the searched mu-term out
replaceMu :: CallingConvention -> XtorArgs Compiled -> (XtorArgs Compiled, Either (STerm Prd Compiled) (STerm Cns Compiled))
replaceMu order MkXtorArgs { prdArgs, cnsArgs }
  | not (all (isSubstPrd order) prdArgs) = 
      case replaceMuPrd order prdArgs of 
        (newPrds, mu) -> (MkXtorArgs newPrds cnsArgs, mu)
  | otherwise =
      case replaceMuCns order cnsArgs of 
        (newCns, mu) -> (MkXtorArgs prdArgs newCns, mu)
  where
    replaceMuPrd :: CallingConvention -> [STerm Prd Compiled] -> ([STerm Prd Compiled], Either (STerm Prd Compiled) (STerm Cns Compiled))
    replaceMuPrd CBV   (mu@(MuAbs ext _ _ _) : prdArgs) = 
      ((BoundVar ext PrdRep (0,0) : prdArgs), Left mu)
    replaceMuPrd order (xtor@(XtorCall ext PrdRep xt args@(MkXtorArgs { prdArgs, cnsArgs })) : ts) 
      | areAllSubst order args =
          case replaceMuPrd order ts of 
            (prds, mu) -> ((xtor : prds), mu)
      | not (all (isSubstPrd order) prdArgs) = 
          case replaceMuPrd order prdArgs of
            (prds, mu) -> (((XtorCall ext PrdRep xt (MkXtorArgs prds cnsArgs)) : ts) , mu)
      | otherwise = 
          case replaceMuCns order cnsArgs of
            (cnss, mu) -> (((XtorCall ext PrdRep xt (MkXtorArgs prdArgs cnss)) : ts), mu)
    replaceMuPrd order (prd : prdArgs) 
      | isSubstPrd order prd = 
          case replaceMuPrd order prdArgs of
            (prds, mu) -> ((prd : prds), mu)
      | otherwise = 
          error $ (show prd) ++ "isn't subsitutable, but should have been!"
    replaceMuPrd _ [] =
      error "Couldn't find and replace a (tilde) mu abstraction, but should have!"

    replaceMuCns :: CallingConvention -> [STerm Cns Compiled] ->  ([STerm Cns Compiled],  Either (STerm Prd Compiled) (STerm Cns Compiled))
    replaceMuCns CBN   (mu@(MuAbs ext _ _ _) : cnsArgs) =
      ((BoundVar ext CnsRep (0,0) : cnsArgs), Right mu)
    replaceMuCns order (xtor@(XtorCall ext CnsRep xt args@(MkXtorArgs { prdArgs, cnsArgs })) : ts)
      | areAllSubst order args =
          case replaceMuCns order ts of 
            (cnss, mu) -> ((xtor : cnss), mu)
      | not (all (isSubstPrd order) prdArgs) =
          case replaceMuPrd order prdArgs of
            (prds, mu) -> (((XtorCall ext CnsRep xt (MkXtorArgs prds cnsArgs)) : ts), mu)
      | otherwise =
          case replaceMuCns order cnsArgs of
            (cnss, mu) -> (((XtorCall ext CnsRep xt (MkXtorArgs prdArgs cnss)) : ts), mu)
    replaceMuCns order (cns : cnsArgs) 
      | isSubstCns order cns =
          case replaceMuCns order cnsArgs of
            (cnss, mu) -> ((cns : cnss), mu)
      | otherwise =
          error $ (show cns) ++ "isn't subsitutable, but should have been!"
    replaceMuCns _ [] =
      error "Couldn't find and replace a (tilde) mu abstraction, but should have!"

-- | Checks wether all producer arguments are substitutable.
-- | The evaluation order determines which arguments are substitutable.
areAllSubst :: CallingConvention -> XtorArgs ext -> Bool
areAllSubst order (MkXtorArgs { prdArgs, cnsArgs }) =
  all (isSubstPrd order) prdArgs && all (isSubstCns order) cnsArgs

-- | subst every producer argument, not containing any mu-abstractions
isSubstPrd :: CallingConvention -> STerm Prd ext -> Bool
isSubstPrd _   (BoundVar _ _ _) = True
isSubstPrd _   (FreeVar _ _ _)  = True
isSubstPrd ord (XtorCall _ _ _ args) = areAllSubst ord args
isSubstPrd _   (XMatch _ _ _ _) = True
isSubstPrd CBV (MuAbs _ _ _ _)  = False
isSubstPrd CBN (MuAbs _ _ _ _)  = True

-- | subst every producer argument, not containing any ~mu-abstractions
isSubstCns :: CallingConvention -> STerm Cns ext -> Bool
isSubstCns _   (BoundVar _ _ _) = True
isSubstCns _   (FreeVar _ _ _)  = True
isSubstCns ord (XtorCall _ _ _ args) = areAllSubst ord args
isSubstCns _   (XMatch _ _ _ _) = True
isSubstCns CBV (MuAbs _ _ _ _)  = True
isSubstCns CBN (MuAbs _ _ _ _)  = False

-- | unpack from Left
fromLeft :: Either a b -> a
fromLeft (Left b)  = b
fromLeft (Right _) = error "expected a left-term but got a right-term"

-- | unpack from Right
fromRight :: Either a b -> b
fromRight (Left _)  = error "expected a right-term but got a left-term"
fromRight (Right a) = a
