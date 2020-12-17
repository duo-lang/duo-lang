module Syntax.Terms where

import Utils

---------------------------------------------------------------------------------
-- Tags
---------------------------------------------------------------------------------

data PrdCns
  = Prd
  | Cns
  deriving (Eq, Show, Ord)

-- | Singleton Type for PrdCns
data PrdCnsRep pc where
  PrdRep :: PrdCnsRep Prd
  CnsRep :: PrdCnsRep Cns
deriving instance Show (PrdCnsRep pc)

---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

data NominalStructural = Nominal | Structural deriving (Eq, Ord, Show)

-- | Name of a constructor/destructor. Starts with an uppercase letter.
data XtorName = MkXtorName { xtorNominalStructural :: NominalStructural, unXtorName :: String } deriving (Eq, Ord, Show)

-- | Name of a free variable. Starts with a lowercase letter.
type FreeVarName = String

---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

data XtorArgs a = MkXtorArgs { prdArgs :: [Term Prd a]
                             , cnsArgs :: [Term Cns a]
                             }
                  deriving (Show)

data Case a = MkCase
  { case_name :: XtorName
  , case_args :: Twice [a]
  , case_cmd  :: Command a
  } deriving (Show)

-- | Two-level de Bruijn indices.
type Index = (Int, Int)

data Term (pc :: PrdCns) a where
  BoundVar :: PrdCnsRep pc -> Index -> Term pc a
  FreeVar  :: PrdCnsRep pc -> FreeVarName -> a -> Term pc a
  XtorCall :: PrdCnsRep pc -> XtorName -> XtorArgs a -> Term pc a
  Match    :: PrdCnsRep pc -> NominalStructural -> [Case a] -> Term pc a
  MuAbs    :: PrdCnsRep pc -> a -> Command a -> Term pc a
  -- The PrdCns parameter describes the result of the abstraction!
deriving instance Show a => Show (Term pc a)

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

data Command a
  = Apply (Term Prd a) (Term Cns a)
  | Print (Term Prd a)
  | Done
  deriving (Show)

