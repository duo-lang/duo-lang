module Eval.ATerms
  ( isValue
  , evalATermComplete
  ) where

import Data.List (find)
import Data.Maybe (fromJust)

import Eval.Eval
import Syntax.ATerms

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
evalATermSingleStep (FVar fv) = do
  (tm,_) <- lookupDef fv
  return (Just tm)
evalATermSingleStep (Ctor xt args) | and (isValue <$> args) = return Nothing
                                   | otherwise = evalArgsSingleStep args >>= 
                                                 \args' -> return (Just (Ctor xt (fromJust args')))
evalATermSingleStep (Match t cases) | not (isValue t) = do 
  t' <- (evalATermSingleStep t)
  return (Just (Match (fromJust t') cases))
evalATermSingleStep (Match (Ctor xt args) cases) =
  case find (\MkACase { acase_name } -> acase_name == xt) cases of
    Nothing -> throwEvalError "Pattern match error"
    Just acase -> return (Just $ atermOpening args (acase_term acase))
evalATermSingleStep (Match _ _) = throwEvalError "unreachable if properly typechecked"
evalATermSingleStep (Dtor xt t args) | not (isValue t) = do
  t' <- evalATermSingleStep t
  return (Just (Dtor xt (fromJust t') args))
evalATermSingleStep (Dtor xt t args) | (not . and) (isValue <$> args) = evalArgsSingleStep args >>=
                                                                        (\args' -> return $ Just (Dtor xt t (fromJust args')))
evalATermSingleStep (Dtor xt (Comatch cocases) args) =
  case find (\MkACase { acase_name } -> acase_name == xt) cocases of
    Nothing -> throwEvalError "Copattern match error"
    Just cocase -> return (Just $ atermOpening args (acase_term cocase))
evalATermSingleStep (Dtor _ _ _) = throwEvalError "unreachable if properly typechecked"
evalATermSingleStep (Comatch _) = return Nothing

evalATermComplete :: ATerm () -> EvalM (ATerm ())
evalATermComplete t = do
  t' <- evalATermSingleStep t
  case t' of
    Nothing -> return t
    Just t'' -> evalATermComplete t''

