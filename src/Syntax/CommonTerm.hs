module Syntax.CommonTerm where

import Data.Text (Text)
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

type family FlipPrdCns (pc :: PrdCns) :: PrdCns where
  FlipPrdCns Prd = Cns
  FlipPrdCns Cns = Prd

flipPrdCns :: PrdCnsRep pc -> PrdCnsRep (FlipPrdCns pc)
flipPrdCns PrdRep = CnsRep
flipPrdCns CnsRep = PrdRep

---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

data NominalStructural = Nominal | Structural deriving (Eq, Ord, Show)

-- | Name of a constructor/destructor. Starts with an uppercase letter.
data XtorName = MkXtorName { xtorNominalStructural :: NominalStructural, unXtorName :: Text } deriving (Eq, Ord, Show)

-- | Name of a free variable. Starts with a lowercase letter.
type FreeVarName = Text

-- | Two-level de Bruijn indices.
type Index = (Int, Int)
