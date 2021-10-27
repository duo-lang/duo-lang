module Eval.ATerms
  ( isValue
  , evalATermComplete
  , evalATermSteps
  ) where

import Data.List (find)
import Data.Maybe (fromJust)

import Lookup
import Eval.Eval
import Syntax.ATerms

---------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------

isValue :: ATerm () -> Bool
isValue (BVar _ _) = True
isValue (FVar _ _) = False
isValue (Ctor _ _ args) = and (isValue <$> args)
isValue (Dtor _ _ _ _) = False
isValue (Match _ _ _ ) = False
isValue (Comatch _ _) = True

isWHNF :: ATerm () -> Bool
isWHNF (BVar _ _) = True
isWHNF (FVar _ _) = False
isWHNF (Ctor _ _ _) = True
isWHNF (Dtor _ _ _ _) = False
isWHNF (Match _ _ _ ) = False
isWHNF (Comatch _ _) = True

evalArgsSingleStep :: [ATerm ()] -> EvalM bs (Maybe [ATerm ()])
evalArgsSingleStep [] = return Nothing
evalArgsSingleStep (a:args) | isValue a = fmap (a:) <$> evalArgsSingleStep args 
                            | otherwise = fmap (:args) <$> evalATermSingleStep a

evalATermSingleStep' :: ATerm () -> EvalOrder -> EvalM bs (Maybe (ATerm ()))
evalATermSingleStep' (BVar _ _) _ = return Nothing
evalATermSingleStep' (FVar _ fv) _ = do
  (tm,_) <- lookupATerm fv
  return (Just tm)
evalATermSingleStep' (Ctor _ xt args) _ | and (isValue <$> args) = return Nothing
                                        | otherwise = evalArgsSingleStep args >>= 
                                                      \args' -> return (Just (Ctor () xt (fromJust args')))
evalATermSingleStep' (Match _ t cases) CBV | not (isValue t) = do
  t' <- (evalATermSingleStep' t CBV)
  return (Just (Match () (fromJust t') cases))
evalATermSingleStep' (Match _ t cases) CBN | not (isWHNF t) = do 
  t' <- (evalATermSingleStep' t CBN)
  return (Just (Match () (fromJust t') cases))
evalATermSingleStep' (Match _ (Ctor _ xt args) cases) _ =
  case find (\MkACase { acase_name } -> acase_name == xt) cases of
    Nothing -> throwEvalError ["Pattern match error"]
    Just acase -> return (Just $ atermOpening args (acase_term acase))
evalATermSingleStep' (Match _ _ _) _ = throwEvalError ["unreachable if properly typechecked"]
evalATermSingleStep' (Dtor _ xt t args) order | not (isValue t) = do
  t' <- evalATermSingleStep' t order
  return (Just (Dtor () xt (fromJust t') args))
evalATermSingleStep' (Dtor _ xt t args) CBV | (not . and) (isValue <$> args) =
  evalArgsSingleStep args >>=
    (\args' -> return $ Just (Dtor () xt t (fromJust args')))
evalATermSingleStep' (Dtor _ xt (Comatch _ cocases) args) _ =
  case find (\MkACase { acase_name } -> acase_name == xt) cocases of
    Nothing -> throwEvalError ["Copattern match error"]
    Just cocase -> return (Just $ atermOpening args (acase_term cocase))
evalATermSingleStep' (Dtor _ _ _ _) _ = throwEvalError ["unreachable if properly typechecked"]
evalATermSingleStep' (Comatch _ _) _ = return Nothing

-- | Choose the correct evaluation strategy
evalATermSingleStep :: ATerm () -> EvalM bs (Maybe (ATerm ()))
evalATermSingleStep t = do
  order <- lookupEvalOrder
  evalATermSingleStep' t order

-- | Return just thef final evaluation result
evalATermComplete :: ATerm () -> EvalM bs (ATerm ())
evalATermComplete t = do
  t' <- evalATermSingleStep t
  case t' of
    Nothing -> return t
    Just t'' -> evalATermComplete t''

-- | Return all intermediate evaluation results
evalATermSteps :: ATerm () -> EvalM bs [ATerm ()]
evalATermSteps t = evalATermSteps' [t] t
  where
    evalATermSteps' :: [ATerm ()] -> ATerm () -> EvalM bs [ATerm ()]
    evalATermSteps' ts t = do
      t' <- evalATermSingleStep t
      case t' of
        Nothing -> return ts
        Just t' -> evalATermSteps' (ts ++ [t']) t'
