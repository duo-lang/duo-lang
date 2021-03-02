module Eval.Eval
  ( EvalOrder(..)
  , runEval
  , eval
  , evalSteps
  -- Asymmetric Terms
  , isValue
  , evalATermComplete
  ) where

import Prelude hiding (lookup)
import Control.Monad.Reader
import Control.Monad.Except
import Data.List (find)
import Data.Map (lookup)
import Data.Maybe (fromJust)
import Prettyprinter

import Pretty.Pretty
import Syntax.Program (Environment, defEnv)
import Syntax.STerms
import Syntax.ATerms
import Utils


data EvalOrder = CBV | CBN

type EvalM a = ReaderT (EvalOrder, Environment) (Except Error) a

runEval :: EvalM a -> EvalOrder -> Environment -> Either Error a
runEval e evalorder env = runExcept (runReaderT e (evalorder, env))

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
evalOneStep :: Pretty a => Command a -> EvalM (Maybe (Command a))
evalOneStep Done = return Nothing
evalOneStep (Print _) = return Nothing
evalOneStep cmd@(Apply (XtorCall PrdRep xt args) (XMatch CnsRep _ cases)) = do
  (MkSCase _ argTypes cmd') <- lookupCase xt cases
  checkArgs cmd argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalOneStep cmd@(Apply (XMatch PrdRep _ cases) (XtorCall CnsRep xt args)) = do
  (MkSCase _ argTypes cmd') <- lookupCase xt cases
  checkArgs cmd argTypes args
  return (Just (commandOpening args cmd')) --reduction is just opening
evalOneStep (Apply prd@(MuAbs PrdRep _ cmd) cns@(MuAbs CnsRep _ cmd')) = do
  evaLOrdAndEnv <- ask
  case fst evaLOrdAndEnv of
    CBV -> return (Just (commandOpeningSingle CnsRep cns cmd))
    CBN -> return (Just (commandOpeningSingle PrdRep prd cmd'))
evalOneStep (Apply (MuAbs PrdRep _ cmd) cns) = return (Just (commandOpeningSingle CnsRep cns cmd))
evalOneStep (Apply prd (MuAbs CnsRep _ cmd)) = return (Just (commandOpeningSingle PrdRep prd cmd))
-- Error handling
evalOneStep cmd@(Apply _ _) = throwError $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                      "\"\n Free variable encountered!")

-- | Return just thef final evaluation result
eval :: Pretty a => Command a -> EvalM (Command a)
eval cmd = do
  cmd' <- evalOneStep cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> eval cmd'

-- | Return all intermediate evaluation results
evalSteps :: Pretty a => Command a -> EvalM [Command a]
evalSteps cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: Pretty a => [Command a] -> Command a -> EvalM [Command a]
    evalSteps' cmds cmd = do
      cmd' <- evalOneStep cmd
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

evalArgsSingleStep :: [ATerm a] -> EvalM (Maybe [ATerm a])
evalArgsSingleStep [] = return Nothing
evalArgsSingleStep (a:args) | isValue a = evalArgsSingleStep args >>= \args' -> case args' of
                                                                                  Nothing -> return Nothing
                                                                                  Just args' -> return $ Just (a:args')
                            | otherwise = (evalATermSingleStep a) >>=
							  (\a' -> return $ Just ((fromJust a') : args))

evalATermSingleStep :: ATerm a -> EvalM (Maybe (ATerm a))
evalATermSingleStep (BVar _) = return Nothing
evalATermSingleStep (FVar x) = do
  ordAndEnv <- ask
  return $ lookup x (defEnv (snd ordAndEnv))
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

evalATermComplete :: ATerm a-> EvalM (ATerm a)
evalATermComplete t = do
  t' <- evalATermSingleStep t
  case t' of
    Nothing -> return t
    Just t'' -> evalATermComplete t''