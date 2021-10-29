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

import Data.Kind (Type)
import Data.List (elemIndex)
import Data.Maybe (isJust, fromJust)

import Syntax.CommonTerm
import Utils

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

type family ATermExt (ext :: Phase) :: Type where
  ATermExt Parsed = Loc
  ATermExt Inferred = Loc
  ATermExt Compiled = ()

-- | Represents one case in a pattern match or copattern match.
-- The `ext` field is used to save additional information, such as source code locations.
--
--        X(x_1,...,x_n) => e
--        ^ ^^^^^^^^^^^     ^
--        |      |          |
--        |  acase_args  acase_term
--        |
--    acase_name
--
data ACase (ext :: Phase) = MkACase
  { acase_ext :: ATermExt ext
  , acase_name :: XtorName
  , acase_args :: [Maybe FreeVarName]
  , acase_term :: ATerm ext
  }

deriving instance (Eq (ACase Parsed))
deriving instance (Eq (ACase Inferred))
deriving instance (Eq (ACase Compiled))
deriving instance (Show (ACase Parsed))
deriving instance (Show (ACase Inferred))
deriving instance (Show (ACase Compiled))
--deriving instance (Ord (ACase Parsed)) -- Missing Ord for Loc.
--deriving instance (Ord (ACase Inferred))
--deriving instance (Ord (ACase Compiled))

-- | An asymmetric term.
-- The `ext` field is used to save additional information, such as source code locations.
-- The `bs` parameter indicates the type of additional information stored at binding sites.
data ATerm (ext :: Phase) where
  -- | A bound variable in the locally nameless system.
  BVar :: ATermExt ext -> Index -> ATerm ext
  -- | A free variable in the locally nameless system.
  FVar :: ATermExt ext -> FreeVarName -> ATerm ext
  -- | A constructor applied to a list of arguments:
  --
  --   C(e_1,...,e_n)
  --
  Ctor :: ATermExt ext -> XtorName -> [ATerm ext] -> ATerm ext
  -- | An expression on which a destructor is called, where the destructor is
  -- applied to a list of arguments:
  --
  --   e.D(e_1,...,e_n)
  --
  Dtor :: ATermExt ext -> XtorName -> ATerm ext -> [ATerm ext] -> ATerm ext
  -- | A pattern match:
  --
  -- match e with { ... }
  --
  Match :: ATermExt ext -> ATerm ext -> [ACase ext] -> ATerm ext
  -- | A copattern match:
  --
  -- comatch { ... }
  --
  Comatch :: ATermExt ext -> [ACase ext] -> ATerm ext

deriving instance (Eq (ATerm Parsed))
deriving instance (Eq (ATerm Inferred))
deriving instance (Eq (ATerm Compiled))
deriving instance (Show (ATerm Parsed))
deriving instance (Show (ATerm Inferred))
deriving instance (Show (ATerm Compiled))

---------------------------------------------------------------------------------
-- Variable Opening and Closing
--
-- For a specification of variable opening and closing we refer to the paper on
-- locally nameless representation cited above.
---------------------------------------------------------------------------------

atermClosingRec :: Int -> [FreeVarName] -> ATerm ext -> ATerm ext
atermClosingRec _ _ bv@(BVar _ _) = bv
atermClosingRec k args fv@(FVar ext v) | isJust (v `elemIndex` args) = BVar ext (k, fromJust (v `elemIndex` args))
                                       | otherwise                   = fv
atermClosingRec k args (Ctor ext xt args') =
  Ctor ext xt (atermClosingRec k args <$> args')
atermClosingRec k args (Dtor ext xt t args') =
  Dtor ext xt (atermClosingRec k args t) (atermClosingRec k args <$> args')
atermClosingRec k args (Match ext t cases) =
  Match ext (atermClosingRec k args t) ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermClosingRec (k + 1) args acase_term }) <$> cases)
atermClosingRec k args (Comatch ext cocases) =
  Comatch ext ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermClosingRec (k + 1) args acase_term }) <$> cocases)

atermClosing :: [FreeVarName] -> ATerm ext -> ATerm ext
atermClosing = atermClosingRec 0

atermOpening :: [ATerm Compiled] -> ATerm Compiled -> ATerm Compiled
atermOpening = atermOpeningRec 0

atermOpeningRec :: Int -> [ATerm Compiled] -> ATerm Compiled -> ATerm Compiled
atermOpeningRec k args bv@(BVar _ (i,j)) | i == k = args !! j
                                         | otherwise = bv
atermOpeningRec _ _ fv@(FVar _ _) = fv
atermOpeningRec k args (Ctor _ xt args') =
  Ctor () xt (atermOpeningRec k args <$> args')
atermOpeningRec k args (Dtor _ xt t args') =
  Dtor () xt (atermOpeningRec k args t) (atermOpeningRec k args <$> args')
atermOpeningRec k args (Match _ t cases) =
  Match () (atermOpeningRec k args t) ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermOpeningRec (k + 1) args acase_term }) <$> cases)
atermOpeningRec k args (Comatch _ cocases) =
  Comatch () ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermOpeningRec (k + 1) args acase_term }) <$> cocases)


---------------------------------------------------------------------------------
-- These functions  translate a locally nameless term into a named representation.
--
-- Use only for prettyprinting! These functions only "undo" the steps in the parser
-- and do not fulfil any semantic properties w.r.t shadowing etc.!
---------------------------------------------------------------------------------

openACase :: ACase ext -> ACase Compiled
openACase MkACase { acase_name, acase_args, acase_term } =
    MkACase { acase_ext = ()
            , acase_name = acase_name
            , acase_args = acase_args
            , acase_term = atermOpening ((\case {Just fv ->  FVar () fv; Nothing -> error "Create Names first!"}) <$> acase_args) (openATermComplete acase_term)
            }

openATermComplete :: ATerm ext -> ATerm Compiled
openATermComplete (BVar _ idx) = BVar () idx
openATermComplete (FVar _ v) = FVar () v
openATermComplete (Ctor _ name args) = Ctor () name (openATermComplete <$> args)
openATermComplete (Dtor _ name t args) = Dtor () name (openATermComplete t) (openATermComplete <$> args)
openATermComplete (Match _ t cases) = Match () (openATermComplete t) (openACase <$> cases)
openATermComplete (Comatch _ cocases) = Comatch () (openACase <$> cocases)

