module Syntax.LocallyNameless where

class LocallyNameless subst vars a | a -> subst, a -> vars where
  openRec  :: Int   -> subst -> a -> a
  closeRec :: Int   -> vars  -> a -> a
  open     ::          subst -> a -> a
  close    ::          vars  -> a -> a

  open  = openRec  0
  close = closeRec 0

class Shiftable direction a | a -> direction where
  shiftRec :: direction -> Int -> a -> a
  shift    :: direction        -> a -> a
  shift = flip shiftRec 0
