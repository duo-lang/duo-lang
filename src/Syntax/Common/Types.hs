module Syntax.Common.Types where

---------------------------------------------------------------------------------
-- Nominal/Structural/Refinement
---------------------------------------------------------------------------------

data NominalStructural = Nominal | Structural | Refinement deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------
-- Refined / NotRefined
---------------------------------------------------------------------------------

data IsRefined = Refined | NotRefined
  deriving (Show, Ord, Eq)

---------------------------------------------------------------------------------
-- IsRec
---------------------------------------------------------------------------------

data IsRec = Recursive | NonRecursive deriving (Show, Eq, Ord)

---------------------------------------------------------------------------------
-- Type Operators
---------------------------------------------------------------------------------

data BinOp where
  FunOp    :: BinOp
  ParOp    :: BinOp
  UnionOp  :: BinOp
  InterOp  :: BinOp
  deriving (Show, Eq)
