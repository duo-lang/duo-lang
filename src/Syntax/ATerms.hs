module Syntax.ATerms
  ( ACase(..)
  , ATerm(..)
  -- Variable Closing
  , atermClosing
  -- Variable Opening
  , atermOpening
  ) where

import Data.List (elemIndex)
import Data.Maybe (isJust, fromJust)

import Syntax.CommonTerm

---------------------------------------------------------------------------------
-- Asymmetric Terms
--
-- We use the locally nameless representation for terms, which combines names for
-- free variables with  anonymous deBruijn indexes for bound variables.
-- The locally namelesss representation is well documented here:
-- https://www.chargueraud.org/softs/ln/
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
-- Variable Closing
---------------------------------------------------------------------------------

atermClosingRec :: Int -> [FreeVarName] -> ATerm a -> ATerm a
atermClosingRec _ _ bv@(BVar _) = bv
atermClosingRec k args fv@(FVar v) | isJust (v `elemIndex` args) = BVar (k, fromJust (v `elemIndex` args))
                                   | otherwise                   = fv
atermClosingRec k args (Ctor xt args') = Ctor xt (atermClosingRec k args <$> args')
atermClosingRec k args (Dtor xt t args') = Dtor xt (atermClosingRec k args t) (atermClosingRec k args <$> args')
atermClosingRec k args (Match t cases) = Match (atermClosingRec k args t) ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermClosingRec (k + 1) args acase_term }) <$> cases)
atermClosingRec k args (Comatch cocases) = Comatch ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermClosingRec (k + 1) args acase_term }) <$> cocases)

atermClosing :: [FreeVarName] -> ATerm a -> ATerm a
atermClosing = atermClosingRec 0

---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

atermOpening :: [ATerm a] -> ATerm a -> ATerm a
atermOpening = atermOpeningRec 0

atermOpeningRec :: Int -> [ATerm a] -> ATerm a -> ATerm a
atermOpeningRec k args bv@(BVar (i,j)) | i == k = args !! j
                                    | otherwise = bv
atermOpeningRec _ _ fv@(FVar _) = fv
atermOpeningRec k args (Ctor xt args') = Ctor xt (atermOpeningRec k args <$> args')
atermOpeningRec k args (Dtor xt t args') = Dtor xt (atermOpeningRec k args t) (atermOpeningRec k args <$> args')
atermOpeningRec k args (Match t cases) = Match (atermOpeningRec k args t) ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermOpeningRec (k + 1) args acase_term }) <$> cases)
atermOpeningRec k args (Comatch cocases) = Comatch ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermOpeningRec (k + 1) args acase_term }) <$> cocases)


