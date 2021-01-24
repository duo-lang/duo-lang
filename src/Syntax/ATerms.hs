module Syntax.ATerms where

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



