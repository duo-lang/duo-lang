module Syntax.Common.Phases where

data Phase where
  Parsed :: Phase
  Inferred :: Phase
  Compiled :: Phase
  deriving (Show, Eq, Ord)
