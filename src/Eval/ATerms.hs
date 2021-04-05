module Eval.ATerms
  ( isValue
  , evalATermComplete
  , evalATermSteps
  ) where

import Data.List (find)
import Data.Maybe (fromJust)

import Eval.Eval
import Syntax.ATerms

---------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------

isValue :: ATerm () bs -> Bool
isValue (BVar _ _) = True
isValue (FVar _ _) = False
isValue (Ctor _ args) = and (isValue <$> args)
isValue (Dtor _ _ _) = False
isValue (Match _ _ ) = False
isValue (Comatch _) = True

isWHNF :: ATerm () bs -> Bool
isWHNF (BVar _ _) = True
isWHNF (FVar _ _) = False
isWHNF (Ctor _ _) = True
isWHNF (Dtor _ _ _) = False
isWHNF (Match _ _ ) = False
isWHNF (Comatch _) = True

evalArgsSingleStep :: [ATerm () bs] -> EvalM bs (Maybe [ATerm () bs])
evalArgsSingleStep [] = return Nothing
evalArgsSingleStep (a:args) | isValue a = fmap (a:) <$> evalArgsSingleStep args 
                            | otherwise = fmap (:args) <$> evalATermSingleStep a

evalATermSingleStep' :: ATerm () bs -> EvalOrder -> EvalM bs (Maybe (ATerm () bs))
evalATermSingleStep' (BVar _ _) _ = return Nothing
evalATermSingleStep' (FVar _ fv) _ = do
  (tm,_) <- lookupDef fv
  return (Just tm)
evalATermSingleStep' (Ctor xt args) _ | and (isValue <$> args) = return Nothing
                                      | otherwise = evalArgsSingleStep args >>= 
                                                      \args' -> return (Just (Ctor xt (fromJust args')))
evalATermSingleStep' (Match t cases) CBV | not (isValue t) = do
  t' <- (evalATermSingleStep' t CBV)
  return (Just (Match (fromJust t') cases))
evalATermSingleStep' (Match t cases) CBN | not (isWHNF t) = do 
  t' <- (evalATermSingleStep' t CBN)
  return (Just (Match (fromJust t') cases))
evalATermSingleStep' (Match (Ctor xt args) cases) _ =
  case find (\MkACase { acase_name } -> acase_name == xt) cases of
    Nothing -> throwEvalError "Pattern match error"
    Just acase -> return (Just $ atermOpening args (acase_term acase))
evalATermSingleStep' (Match _ _) _ = throwEvalError "unreachable if properly typechecked"
evalATermSingleStep' (Dtor xt t args) order | not (isValue t) = do
  t' <- evalATermSingleStep' t order
  return (Just (Dtor xt (fromJust t') args))
evalATermSingleStep' (Dtor xt t args) CBV | (not . and) (isValue <$> args) =
  evalArgsSingleStep args >>=
    (\args' -> return $ Just (Dtor xt t (fromJust args')))
evalATermSingleStep' (Dtor xt (Comatch cocases) args) _ =
  case find (\MkACase { acase_name } -> acase_name == xt) cocases of
    Nothing -> throwEvalError "Copattern match error"
    Just cocase -> return (Just $ atermOpening args (acase_term cocase))
evalATermSingleStep' (Dtor _ _ _) _ = throwEvalError "unreachable if properly typechecked"
evalATermSingleStep' (Comatch _) _ = return Nothing

-- | Choose the correct evaluation strategy
evalATermSingleStep :: ATerm () bs -> EvalM bs (Maybe (ATerm () bs))
evalATermSingleStep t = do
  order <- lookupEvalOrder
  evalATermSingleStep' t order

-- | Return just thef final evaluation result
evalATermComplete :: ATerm () bs -> EvalM bs (ATerm () bs)
evalATermComplete t = do
  t' <- evalATermSingleStep t
  case t' of
    Nothing -> return t
    Just t'' -> evalATermComplete t''

-- | Return all intermediate evaluation results
evalATermSteps :: ATerm () bs -> EvalM bs [ATerm () bs]
evalATermSteps t = evalATermSteps' [t] t
  where
    evalATermSteps' :: [ATerm () bs] -> ATerm () bs -> EvalM bs [ATerm () bs]
    evalATermSteps' ts t = do
      t' <- evalATermSingleStep t
      case t' of
        Nothing -> return ts
        Just t' -> evalATermSteps' (ts ++ [t']) t'
