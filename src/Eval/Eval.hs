module Eval.Eval
  ( EvalOrder(..)
  , runEval
  , eval
  , evalSteps
  -- Asymmetric Terms
  , isValue
  , evalATermComplete
  ) where

import Control.Monad.Reader
import Control.Monad.Except
import Data.List (find)
import qualified Data.Map as M (lookup)
import Data.Maybe (fromJust)
import Prettyprinter

import Pretty.Pretty
import Syntax.Program (Environment, defEnv, prdEnv, cnsEnv)
import Syntax.STerms
import Syntax.ATerms
import Utils


data EvalOrder = CBV | CBN

type EvalM a = ReaderT (EvalOrder, Environment) (Except Error) a

runEval :: EvalM a -> EvalOrder -> Environment -> Either Error a
runEval e evalorder env = runExcept (runReaderT e (evalorder, env))

---------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------

lookupCase :: XtorName -> [SCase a] -> EvalM (SCase a)
lookupCase xt cases = case find (\MkSCase { scase_name } -> xt == scase_name) cases of
  Just pmcase -> return pmcase
  Nothing -> throwError $ EvalError $ unlines ["Error during evaluation. The xtor: "
                                              , unXtorName xt
                                              , "doesn't occur in match."
                                              ]

lengthXtorArgs :: XtorArgs a -> Twice Int
lengthXtorArgs MkXtorArgs { prdArgs, cnsArgs } = Twice (length prdArgs) (length cnsArgs)

checkArgs :: Pretty a => Command a -> Twice [a] -> XtorArgs a -> EvalM ()
checkArgs cmd argTypes args =
  if fmap length argTypes == lengthXtorArgs args
  then return ()
  else throwError $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                               "\"\nArgument lengths don't coincide.")

-- | Returns Nothing if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalSTermOnce :: Command () -> EvalM (Maybe (Command ()))
evalSTermOnce Done = return Nothing
evalSTermOnce (Print _) = return Nothing
evalSTermOnce (Apply prd cns) = evalApplyOnce prd cns

evalApplyOnce :: STerm Prd () -> STerm Cns () -> EvalM (Maybe (Command ()))
-- Free variables have to be looked up in the environment.
evalApplyOnce (FreeVar PrdRep n _) cns = do
  env <- asks snd
  case M.lookup n (prdEnv env) of
    Nothing -> throwError $ EvalError $ "Encountered unbound free variable: " ++ show n
    Just prd -> return (Just (Apply prd cns))
evalApplyOnce prd (FreeVar CnsRep n _) = do
  env <- asks snd
  case M.lookup n (cnsEnv env) of
    Nothing -> throwError $ EvalError $ "Encountered unbound free variable: " ++ show n
    Just cns -> return (Just (Apply prd cns))
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
  order <- asks fst
  case order of
    CBV -> return (Just (commandOpeningSingle CnsRep cns cmd))
    CBN -> return (Just (commandOpeningSingle PrdRep prd cmd'))
evalApplyOnce (MuAbs PrdRep _ cmd) cns = return (Just (commandOpeningSingle CnsRep cns cmd))
evalApplyOnce prd (MuAbs CnsRep _ cmd) = return (Just (commandOpeningSingle PrdRep prd cmd))
-- Bound variables should not occur at the toplevel during evaluation.
evalApplyOnce (BoundVar PrdRep i) _ = throwError $ EvalError $ "Found bound variable during evaluation. Index: " ++ show i
evalApplyOnce _ (BoundVar CnsRep i) = throwError $ EvalError $ "Found bound variable during evaluation. Index: " ++ show i
-- Match applied to Match, or Xtor to Xtor can't evaluate
evalApplyOnce (XMatch _ _ _) (XMatch _ _ _) = throwError $ EvalError "Cannot evaluate match applied to match"
evalApplyOnce (XtorCall _ _ _) (XtorCall _ _ _) = throwError $ EvalError "Cannot evaluate constructor applied to destructor"

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

---------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------

isValue :: ATerm a -> Bool
isValue (BVar _) = True
isValue (FVar _) = False
isValue (Ctor _ args) = and (isValue <$> args)
isValue (Dtor _ _ _) = False
isValue (Match _ _ ) = False
isValue (Comatch _) = True

evalArgsSingleStep :: [ATerm ()] -> EvalM (Maybe [ATerm ()])
evalArgsSingleStep [] = return Nothing
evalArgsSingleStep (a:args) | isValue a = fmap (a:) <$> evalArgsSingleStep args 
                            | otherwise = fmap (:args) <$> evalATermSingleStep a

evalATermSingleStep :: ATerm () -> EvalM (Maybe (ATerm ()))
evalATermSingleStep (BVar _) = return Nothing
evalATermSingleStep (FVar x) = do
  env <- asks snd
  return $ M.lookup x (defEnv env)
evalATermSingleStep (Ctor xt args) | and (isValue <$> args) = return Nothing
                                   | otherwise = evalArgsSingleStep args >>= 
                                                 \args' -> return (Just (Ctor xt (fromJust args')))
evalATermSingleStep (Match t cases) | not (isValue t) = do 
  t' <- (evalATermSingleStep t)
  return (Just (Match (fromJust t') cases))
evalATermSingleStep (Match (Ctor xt args) cases) =
  case find (\MkACase { acase_name } -> acase_name == xt) cases of
    Nothing -> throwError $ EvalError "Pattern match error"
    Just acase -> return (Just $ atermOpening args (acase_term acase))
evalATermSingleStep (Match _ _) = throwError $ EvalError ("unreachable if properly typechecked")
evalATermSingleStep (Dtor xt t args) | not (isValue t) = do
  t' <- evalATermSingleStep t
  return (Just (Dtor xt (fromJust t') args))
evalATermSingleStep (Dtor xt t args) | (not . and) (isValue <$> args) = evalArgsSingleStep args >>= 
                                                                        (\args' -> return $ Just (Dtor xt t (fromJust args')))
evalATermSingleStep (Dtor xt (Comatch cocases) args) =
  case find (\MkACase { acase_name } -> acase_name == xt) cocases of
    Nothing -> throwError $ EvalError ("Copattern match error")
    Just cocase -> return (Just $ atermOpening args (acase_term cocase))
evalATermSingleStep (Dtor _ _ _) = throwError $ EvalError ("unreachable if properly typechecked")
evalATermSingleStep (Comatch _) = return Nothing

evalATermComplete :: ATerm () -> EvalM (ATerm ())
evalATermComplete t = do
  t' <- evalATermSingleStep t
  case t' of
    Nothing -> return t
    Just t'' -> evalATermComplete t''
