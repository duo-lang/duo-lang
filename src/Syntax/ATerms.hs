module Syntax.ATerms
  ( ACase(..)
  , ATerm(..)
  -- Variable Opening
  , atermClosing
  ) where

import Data.List (elemIndex)
import Data.Maybe (isJust, fromJust)

import Syntax.CommonTerm

---------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------

data ACase a = MkACase
  { acase_name :: XtorName
  , acase_args :: [a]
  , acase_term :: ATerm a
  } deriving (Eq, Show, Ord)

data ATerm a where
  BVar :: Index -> ATerm a
  FVar :: FreeVarName -> ATerm a
  Ctor :: XtorName -> [ATerm a] -> ATerm a
  Dtor :: XtorName -> ATerm a -> [ATerm a] -> ATerm a
  Match :: ATerm a -> [ACase a] -> ATerm a
  Comatch :: [ACase a] -> ATerm a
  deriving (Eq, Show, Ord)

---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

atermClosingRec :: Int -> [FreeVarName] -> ATerm a -> ATerm a
atermClosingRec _ _ bv@(BVar _) = bv
atermClosingRec k args fv@(FVar v) | isJust (v `elemIndex` args) = BVar (k, fromJust (v `elemIndex` args))
                                   | otherwise                   = fv
atermClosingRec k args (Ctor xt args') = Ctor xt (atermClosingRec k args <$> args')
atermClosingRec k args (Dtor xt t args') = Dtor xt (atermClosingRec k args t) (atermClosingRec k args <$> args')
atermClosingRec k args (Match t cases) = Match (atermClosingRec k args t) ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermClosingRec (k + 1) args acase_term }) <$> cases)
atermClosingRec k args (Comatch cocases) = Comatch ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermClosingRec (k + 1) args acase_term }) <$> cocases)

atermClosing :: [FreeVarName] -> ATerm () -> ATerm ()
atermClosing = atermClosingRec 0
