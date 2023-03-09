module Syntax.LocallyNameless where

---------------------------------------------------------------------------------
-- de Bruijn indices
---------------------------------------------------------------------------------

-- | Two-level de Bruijn indices.
type Index = (Int, Int)

class LocallyNameless subst vars a | a -> subst, a -> vars where
  openRec  :: Int   -> subst -> a -> a
  closeRec :: Int   -> vars  -> a -> a
  open     ::          subst -> a -> a
  close    ::          vars  -> a -> a

  open  = openRec  0
  close = closeRec 0

data ShiftDirection = ShiftUp | ShiftDown
  deriving (Show, Eq)

class Shiftable a where
  shiftRec :: ShiftDirection -> Int -> a -> a
  shift    :: ShiftDirection        -> a -> a
  shift = flip shiftRec 0
