module Syntax.CommonTerm where

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
deriving instance Eq (PrdCnsRep pc)

---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

data NominalStructural = Nominal | Structural deriving (Eq, Ord, Show)

-- | Name of a constructor/destructor. Starts with an uppercase letter.
data XtorName = MkXtorName { xtorNominalStructural :: NominalStructural, unXtorName :: String } deriving (Eq, Ord, Show)

-- | Name of a free variable. Starts with a lowercase letter.
type FreeVarName = String

-- | Two-level de Bruijn indices.
type Index = (Int, Int)
