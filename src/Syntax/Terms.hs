module Syntax.Terms where

import Data.Map (Map)

import Utils

---------------------------------------------------------------------------------
-- Term/commmand Syntax
---------------------------------------------------------------------------------

type XtorName = String -- start with uppercase
type FreeVarName = String -- start with lowercase
type TypeIdentifierName = String -- start with uppercase

data DataOrCodata = Data | Codata deriving (Eq,Show)
showDataOrCodata :: DataOrCodata -> String
showDataOrCodata Data = "+"
showDataOrCodata Codata = "-"

data PrdOrCns = Prd | Cns deriving (Eq,Show,Ord)

type XtorArgs a = Twice [Term a]
getArg :: Int -> PrdOrCns -> XtorArgs a -> Term a
getArg j Prd (Twice prds _) = prds !! j
getArg j Cns (Twice _ cnss) = cnss !! j

type MatchCase a = (XtorName, Twice [a], Command a)

data Term a =
    BoundVar Int PrdOrCns Int -- de bruijn indices
  | FreeVar FreeVarName a
  | XtorCall DataOrCodata XtorName (XtorArgs a)
  | Match DataOrCodata [MatchCase a]
  | MuAbs PrdOrCns a (Command a) deriving (Eq,Show)
  -- The PrdOrCns parameter describes the type of variable that is being bound by the mu.
  -- If a mu binds a producer, it is itself a consumer and vice versa.
  -- MuAbs Cns == \mu, MuAbs Prd == \tilde{\mu}.

-- determines if the term is a producer or a consumer
-- is only defined for closed terms, since we cannot distinguish producer from consumer variable names
-- We distinguish them only in the mathematical formaliazation of the syntax, not in the actual implementation
termPrdOrCns :: Term a -> PrdOrCns
termPrdOrCns (XtorCall Data _ _)   = Prd
termPrdOrCns (XtorCall Codata _ _) = Cns
termPrdOrCns (Match Data _)        = Cns
termPrdOrCns (Match Codata _)      = Prd
termPrdOrCns (MuAbs Prd _ _)       = Cns
termPrdOrCns (MuAbs Cns _ _)       = Prd
termPrdOrCns (BoundVar _ pc _)     = pc
termPrdOrCns (FreeVar _ _)         = error "termPrdOrCns: free variable found"

data Command a = Apply (Term a) (Term a) | Print (Term a) | Done deriving (Eq,Show)

type TermEnvironment = Map FreeVarName (Term ())
