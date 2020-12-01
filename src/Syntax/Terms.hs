module Syntax.Terms where

import Utils

---------------------------------------------------------------------------------
-- Tags
---------------------------------------------------------------------------------

data DataCodata
  = Data
  | Codata
  deriving (Eq, Show, Ord)

-- | Singleton Type for DataCodata
data DataCodataRep a where
  DataRep   :: DataCodataRep Data
  CodataRep :: DataCodataRep Codata

data PrdCns
  = Prd
  | Cns
  deriving (Eq, Show, Ord)

-- | Singleton Type for PrdCns
data PrdCnsRep a where
  PrdRep :: PrdCnsRep Prd
  CnsRep :: PrdCnsRep Cns

---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

-- | Name of a constructor/destructor. Starts with an uppercase letter.
data XtorName = MkXtorName { unXtorName :: String } deriving (Eq, Ord, Show)

-- | Name of a free variable. Starts with a lowercase letter.
type FreeVarName = String

---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

type XtorArgs a = Twice [Term a]

data Case a = MkCase
  { case_name :: XtorName
  , case_args :: Twice [a]
  , case_cmd  :: Command a
  } deriving (Show, Eq)

type Index = (Int, Int)

data Term a where
  BoundVar :: Index -> PrdCns -> Term a -- de bruijn indices
  FreeVar :: FreeVarName -> a -> Term a
  XtorCall :: DataCodata -> XtorName -> XtorArgs a -> Term a
  Match :: DataCodata -> [Case a] -> Term a
  MuAbs :: PrdCns -> a -> Command a -> Term a
  -- The PrdOrCns parameter describes the type of variable that is being bound by the mu.
  -- If a mu binds a producer, it is itself a consumer and vice versa.
  -- MuAbs Cns == \mu, MuAbs Prd == \tilde{\mu}.
  deriving (Eq,Show)

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

data Command a
  = Apply (Term a) (Term a)
  | Print (Term a)
  | Done
  deriving (Eq,Show)

