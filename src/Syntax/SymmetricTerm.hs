module Syntax.SymmetricTerm
  ( module Syntax.CommonTerm
  , XtorArgs(..)
  , SCase(..)
  , STerm(..)
  , Command(..)
  ) where

import Utils
import Syntax.CommonTerm

---------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------

data XtorArgs a = MkXtorArgs { prdArgs :: [STerm Prd a]
                             , cnsArgs :: [STerm Cns a]
                             }
                  deriving (Show)

data SCase a = MkSCase
  { scase_name :: XtorName
  , scase_args :: Twice [a]
  , scase_cmd  :: Command a
  } deriving (Show)

data STerm (pc :: PrdCns) a where
  BoundVar :: PrdCnsRep pc -> Index -> STerm pc a
  FreeVar  :: PrdCnsRep pc -> FreeVarName -> a -> STerm pc a
  XtorCall :: PrdCnsRep pc -> XtorName -> XtorArgs a -> STerm pc a
  XMatch   :: PrdCnsRep pc -> NominalStructural -> [SCase a] -> STerm pc a
  MuAbs    :: PrdCnsRep pc -> a -> Command a -> STerm pc a
  -- The PrdCns parameter describes the result of the abstraction!
deriving instance Show a => Show (STerm pc a)

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

data Command a
  = Apply (STerm Prd a) (STerm Cns a)
  | Print (STerm Prd a)
  | Done
  deriving (Show)

