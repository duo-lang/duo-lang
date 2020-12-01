module Syntax.Terms where

import Utils

---------------------------------------------------------------------------------
-- Tags
---------------------------------------------------------------------------------

data DataCodata
  = Data
  | Codata
  deriving (Eq, Show, Ord)

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

data XtorArgs a = MkXtorArgs { prdArgs :: [Term Prd a]
                             , cnsArgs :: [Term Prd a]
                             }
                  deriving (Eq, Show)

data Case a = MkCase
  { case_name :: XtorName
  , case_args :: Twice [a]
  , case_cmd  :: Command a
  } deriving (Show, Eq)

type Index = (Int, Int)

data Term (pc :: PrdCns) a where
  BoundVar :: PrdCns -> Index -> Term Prd a -- de bruijn indices
  FreeVar  :: PrdCns -> FreeVarName -> a -> Term Prd a
  XtorCall :: PrdCns -> XtorName -> XtorArgs a -> Term Prd a
  Match    :: PrdCns -> [Case a] -> Term Prd a
  MuAbs    :: PrdCns -> a -> Command a -> Term Prd a
  -- The PrdOrCns parameter describes the type of variable that is being bound by the mu.
  -- If a mu binds a producer, it is itself a consumer and vice versa.
  -- MuAbs Cns == \mu, MuAbs Prd == \tilde{\mu}.
deriving instance Eq a => Eq (Term pc a)
deriving instance Show a => Show (Term pc a)

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

data Command a
  = Apply (Term Prd a) (Term Prd a)
  | Print (Term Prd a)
  | Done
  deriving (Eq,Show)

