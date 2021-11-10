module Eval.ATerms
  ( isValue
  , evalATermComplete
  , evalATermSteps
  ) where

import Data.List (find)
import Data.Maybe (fromJust)

import Lookup ( lookupATerm )
import Eval.Eval
    ( throwEvalError, lookupEvalOrder, EvalM)
import Syntax.ATerms
import Syntax.Kinds
import Translate.Translate

---------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------

isValue :: ATerm Compiled -> Bool
isValue (Dtor _ _ _ _) = False
isValue (Match _ _ _ ) = False
isValue (Comatch _ _) = True

isWHNF :: ATerm Compiled -> Bool
isWHNF (Dtor _ _ _ _) = False
isWHNF (Match _ _ _ ) = False
isWHNF (Comatch _ _) = True

evalArgsSingleStep :: [ATerm Compiled] -> EvalM (Maybe [ATerm Compiled])
evalArgsSingleStep [] = return Nothing
evalArgsSingleStep (a:args) | isValue a = fmap (a:) <$> evalArgsSingleStep args 
                            | otherwise = fmap (:args) <$> evalATermSingleStep a

evalATermSingleStep' :: ATerm Compiled -> CallingConvention -> EvalM (Maybe (ATerm Compiled))
evalATermSingleStep' (Match _ t cases) CBV | not (isValue t) = do
  t' <- (evalATermSingleStep' t CBV)
  return (Just (Match () (fromJust t') cases))
evalATermSingleStep' (Match _ t cases) CBN | not (isWHNF t) = do 
  t' <- (evalATermSingleStep' t CBN)
  return (Just (Match () (fromJust t') cases))
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
evalATermSingleStep :: ATerm Compiled -> EvalM (Maybe (ATerm Compiled))
evalATermSingleStep t = do
  order <- lookupEvalOrder
  evalATermSingleStep' t order

-- | Return just thef final evaluation result
evalATermComplete :: ATerm Compiled -> EvalM (ATerm Compiled)
evalATermComplete t = do
  t' <- evalATermSingleStep t
  case t' of
    Nothing -> return t
    Just t'' -> evalATermComplete t''

-- | Return all intermediate evaluation results
evalATermSteps :: ATerm Compiled -> EvalM [ATerm Compiled]
evalATermSteps t = evalATermSteps' [t] t
  where
    evalATermSteps' :: [ATerm Compiled] -> ATerm Compiled -> EvalM [ATerm Compiled]
    evalATermSteps' ts t = do
      t' <- evalATermSingleStep t
      case t' of
        Nothing -> return ts
        Just t' -> evalATermSteps' (ts ++ [t']) t'
