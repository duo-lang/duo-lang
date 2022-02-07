module Syntax.Common where

import Data.Text (Text)

---------------------------------------------------------------------------------
-- Phases
---------------------------------------------------------------------------------

data Phase where
  Parsed :: Phase
  Inferred :: Phase
  Compiled :: Phase
  deriving (Show, Eq, Ord)

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

data IsRec = Recursive | NonRecursive

---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

newtype ModuleName = ModuleName { unModuleName :: Text }

data NominalStructural = Nominal | Structural deriving (Eq, Ord, Show)

-- | Name of a constructor/destructor. Starts with an uppercase letter.
data XtorName = MkXtorName { xtorNominalStructural :: NominalStructural, unXtorName :: Text } deriving (Eq, Ord, Show)

-- | Name of a free variable. Starts with a lowercase letter.
type FreeVarName = Text

-- | Two-level de Bruijn indices.
type Index = (Int, Int)

---------------------------------------------------------------------------------
-- Operators
---------------------------------------------------------------------------------

-- | Binary Type Operators
data BinOpSym where
  UnionOp :: BinOpSym
  InterOp :: BinOpSym
  OtherOp :: Text -> BinOpSym
  deriving (Show, Eq)

data Variance = Covariant | Contravariant
  deriving (Show, Eq, Ord)

newtype Precedence = MkPrecedence { unPrecedence :: Int }
  deriving (Show, Eq, Ord)

data Assoc = LeftAssoc | RightAssoc
    deriving (Show, Eq, Ord)

data BinOp = BinOp
    { symbol :: BinOpSym
    , assoc :: Assoc
    , prec :: Precedence
    }

unionOp :: BinOp
unionOp = BinOp { symbol = UnionOp
                , assoc = LeftAssoc
                , prec = MkPrecedence 1
                }

interOp :: BinOp
interOp = BinOp { symbol = InterOp
                , assoc = LeftAssoc
                , prec = MkPrecedence 2
                }