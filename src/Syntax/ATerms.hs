module Syntax.ATerms
  ( ACase(..)
  , ATerm(..)
  -- Variable Closing
  , atermClosing
  -- Variable Opening
  , atermOpening
  -- Transform to named representation for prettyprinting
  , openATermComplete
  , module Syntax.CommonTerm
  ) where

import Data.List (elemIndex)
import Data.Maybe (isJust, fromJust)

import Syntax.CommonTerm

---------------------------------------------------------------------------------
-- # Asymmetric Terms
--
-- Asymmetric terms are called "asymmetric" since they have a bias towards terms
-- which "produce" a result (in distinction to terms which "consume" something).
-- This terminology is motivated by their distinction w.r.t. the symmetric terms
-- which support both sorts of terms on equal footing.
--
-- ## Variable representation
--
-- We use the locally nameless representation for terms, which combines names for
-- free variables with  anonymous deBruijn indexes for bound variables.
-- The locally namelesss representation is well documented here:
-- https://www.chargueraud.org/softs/ln/
---------------------------------------------------------------------------------

-- | Represents one case in a pattern match or copattern match.
--
--        X(x_1,...,x_n) => e
--        ^ ^^^^^^^^^^^     ^
--        |      |          |
--        |  acase_args  acase_term
--        |
--    acase_name
--
data ACase ext bs = MkACase
  { acase_name :: XtorName
  , acase_args :: [bs]
  , acase_term :: ATerm ext bs
  } deriving (Eq, Show, Ord)

-- | An asymmetric term.
-- The bs parameter indicates the type of additional information stored at binding sites.
data ATerm ext bs where
  -- | A bound variable in the locally nameless system.
  BVar :: Index -> ATerm ext bs
  -- | A free variable in the locally nameless system.
  FVar :: FreeVarName -> ATerm ext bs
  -- | A constructor applied to a list of arguments:
  --
  --   C(e_1,...,e_n)
  --
  Ctor :: XtorName -> [ATerm ext bs] -> ATerm ext bs
  -- | An expression on which a destructor is called, where the destructor is
  -- applied to a list of arguments:
  --
  --   e.D(e_1,...,e_n)
  --
  Dtor :: XtorName -> ATerm ext bs -> [ATerm ext bs] -> ATerm ext bs
  -- | A pattern match:
  --
  -- match e with { ... }
  --
  Match :: ATerm ext bs -> [ACase ext bs] -> ATerm ext bs
  -- | A copattern match:
  --
  -- comatch { ... }
  --
  Comatch :: [ACase ext bs] -> ATerm ext bs
  deriving (Eq, Show, Ord)

---------------------------------------------------------------------------------
-- Variable Opening and Closing
--
-- For a specification of variable opening and closing we refer to the paper on
-- locally nameless representation cited above.
---------------------------------------------------------------------------------

atermClosingRec :: Int -> [FreeVarName] -> ATerm () a -> ATerm () a
atermClosingRec _ _ bv@(BVar _) = bv
atermClosingRec k args fv@(FVar v) | isJust (v `elemIndex` args) = BVar (k, fromJust (v `elemIndex` args))
                                   | otherwise                   = fv
atermClosingRec k args (Ctor xt args') =
  Ctor xt (atermClosingRec k args <$> args')
atermClosingRec k args (Dtor xt t args') =
  Dtor xt (atermClosingRec k args t) (atermClosingRec k args <$> args')
atermClosingRec k args (Match t cases) =
  Match (atermClosingRec k args t) ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermClosingRec (k + 1) args acase_term }) <$> cases)
atermClosingRec k args (Comatch cocases) =
  Comatch ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermClosingRec (k + 1) args acase_term }) <$> cocases)

atermClosing :: [FreeVarName] -> ATerm () a -> ATerm () a
atermClosing = atermClosingRec 0

atermOpening :: [ATerm () a] -> ATerm () a -> ATerm () a
atermOpening = atermOpeningRec 0

atermOpeningRec :: Int -> [ATerm () a] -> ATerm () a -> ATerm () a
atermOpeningRec k args bv@(BVar (i,j)) | i == k = args !! j
                                       | otherwise = bv
atermOpeningRec _ _ fv@(FVar _) = fv
atermOpeningRec k args (Ctor xt args') =
  Ctor xt (atermOpeningRec k args <$> args')
atermOpeningRec k args (Dtor xt t args') =
  Dtor xt (atermOpeningRec k args t) (atermOpeningRec k args <$> args')
atermOpeningRec k args (Match t cases) =
  Match (atermOpeningRec k args t) ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermOpeningRec (k + 1) args acase_term }) <$> cases)
atermOpeningRec k args (Comatch cocases) =
  Comatch ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermOpeningRec (k + 1) args acase_term }) <$> cocases)


---------------------------------------------------------------------------------
-- These functions  translate a locally nameless term into a named representation.
--
-- Use only for prettyprinting! These functions only "undo" the steps in the parser
-- and do not fulfil any semantic properties w.r.t shadowing etc.!
---------------------------------------------------------------------------------

openACase :: ACase () FreeVarName -> ACase () FreeVarName
openACase MkACase { acase_name, acase_args, acase_term } =
    MkACase { acase_name = acase_name
            , acase_args = acase_args
            , acase_term = atermOpening ((\fv -> FVar fv) <$> acase_args) (openATermComplete acase_term)
            }

openATermComplete :: ATerm () FreeVarName -> ATerm () FreeVarName
openATermComplete (BVar idx) = BVar idx
openATermComplete (FVar v) = FVar v
openATermComplete (Ctor name args) = Ctor name (openATermComplete <$> args)
openATermComplete (Dtor name t args) = Dtor name (openATermComplete t) (openATermComplete <$> args)
openATermComplete (Match t cases) = Match (openATermComplete t) (openACase <$> cases)
openATermComplete (Comatch cocases) = Comatch (openACase <$> cocases)



