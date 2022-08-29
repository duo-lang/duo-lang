module Loc where

import Text.Megaparsec.Pos ( mkPos, SourcePos(SourcePos) )

----------------------------------------------------------------------------------
-- Source code locations
----------------------------------------------------------------------------------

data Loc = Loc !SourcePos !SourcePos
  deriving (Eq, Ord)

instance Show Loc where
  show (Loc _s1 _s2) = "<loc>"

defaultLoc :: Loc
defaultLoc = Loc (SourcePos "DEFAULTFILELOC" (mkPos 1) (mkPos 1)) (SourcePos "DEFAULTFILELOC" (mkPos 1) (mkPos 1))

-- | A typeclass for things which can be mapped to a source code location.
class HasLoc a where
  getLoc :: a -> Loc

-- | A typeclass for things to which we want to attach a source code location.
class AttachLoc a where
  attachLoc :: Loc -> a -> a
