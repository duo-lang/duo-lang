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
import Data.Maybe (fromJust)
import Prettyprinter

import Pretty.Pretty
import Syntax.STerms
import Syntax.ATerms
import Utils


data EvalOrder = CBV | CBN

type EvalM a = (ReaderT EvalOrder (Except Error)) a

runEval :: EvalM a -> EvalOrder -> Either Error a
runEval e evalorder = runExcept (runReaderT e evalorder)

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
  evalOrder <- ask
  case evalOrder of
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
isValue (FVar _) = True
isValue (Ctor _ args) = and (isValue <$> args)
isValue (Dtor _ _ _) = False
isValue (Match _ _ ) = False
isValue (Comatch _) = True

evalArgsSingleStep :: [ATerm a] -> Maybe [ATerm a]
evalArgsSingleStep [] = Nothing
evalArgsSingleStep (a:args) | isValue a = case evalArgsSingleStep args of
                                         Nothing -> Nothing
                                         Just args' -> Just (a:args')
                            | otherwise = Just ((fromJust $ evalATermSingleStep a) : args)

evalATermSingleStep :: ATerm a -> Maybe (ATerm a)
evalATermSingleStep (BVar _) = Nothing
evalATermSingleStep (FVar _) = Nothing
evalATermSingleStep (Ctor xt args) | and (isValue <$> args) = Nothing
                                   | otherwise = Just (Ctor xt (fromJust (evalArgsSingleStep args)))
evalATermSingleStep (Match t cases) | not (isValue t) = Just (Match (fromJust (evalATermSingleStep t)) cases)
evalATermSingleStep (Match (Ctor xt args) cases) =
  case find (\MkACase { acase_name } -> acase_name == xt) cases of
    Nothing -> error "Pattern match error"
    Just acase -> Just $ atermOpening args (acase_term acase)
evalATermSingleStep (Match _ _) = error "unreachable if properly typechecked"
evalATermSingleStep (Dtor xt t args) | not (isValue t) = Just (Dtor xt (fromJust (evalATermSingleStep t)) args)
evalATermSingleStep (Dtor xt t args) | (not . and) (isValue <$> args) = Just (Dtor xt t (fromJust $ evalArgsSingleStep args))
evalATermSingleStep (Dtor xt (Comatch cocases) args) =
  case find (\MkACase { acase_name } -> acase_name == xt) cocases of
    Nothing -> error "Copattern match error"
    Just cocase -> Just $ atermOpening args (acase_term cocase)
evalATermSingleStep (Dtor _ _ _) = error "unreachable if properly typechecked"
evalATermSingleStep (Comatch _) = Nothing

evalATermComplete :: ATerm a-> ATerm a
evalATermComplete t = case evalATermSingleStep t of
  Nothing -> t
  Just t' -> evalATermComplete t'

