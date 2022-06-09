module LSP.MegaparsecToLSP where

import Data.List (sortBy )
import Data.Map (Map)
import Data.Map qualified as M
import Text.Megaparsec
    ( SourcePos(SourcePos), unPos )
import Utils ( Loc(..) )
import Language.LSP.Types
    ( Position(..),
      Range(..)
    )

-- | Transform a Megaparsec "SourcePos" to a LSP "Position".
-- Megaparsec and LSP's numbering conventions don't align!
posToPosition :: SourcePos -> Position
posToPosition (SourcePos _ line column) =
  Position { _line = unPos line - 1, _character = unPos column - 1}

-- | Convert the Loc that we use internally to LSP's Range type.
locToRange :: Loc -> Range
locToRange (Loc startPos endPos) =
  Range { _start = posToPosition startPos
        , _end   = posToPosition endPos
        }

locToStartRange :: Loc -> Range         
locToStartRange (Loc startPos _endPos) =
  Range { _start = posToPosition startPos
        , _end   = posToPosition startPos
        }

locToEndRange :: Loc -> Range         
locToEndRange (Loc _startPos endPos) =
  Range { _start = posToPosition endPos
        , _end   = posToPosition endPos
        }

lookupPos :: Position -> Loc -> Bool 
lookupPos (Position l _) (Loc begin end) =
  let
    (Position l1 _) = posToPosition  begin
    (Position l2 _) = posToPosition end 
  in
    l1 <= l && l <= l2

---------------------------------------------------------------------------------
-- Computations on positions and ranges
---------------------------------------------------------------------------------

-- Define an ordering on Positions
positionOrd :: Position -> Position -> Ordering
positionOrd (Position line1 column1) (Position line2 column2) =
  case compare line1 line2 of
    LT -> LT
    EQ -> compare column1 column2
    GT -> GT

-- | Check whether the first position comes textually before the second position.
before :: Position -> Position -> Bool
before pos1 pos2 = case positionOrd pos1 pos2 of
  LT -> True
  EQ -> True
  GT -> False

-- | Check whether a given position lies within a given range
inRange :: Position -> Range -> Bool
inRange pos (Range startPos endPos) = before startPos pos && before pos endPos

-- | Order ranges according to their starting position
rangeOrd :: Range -> Range -> Ordering
rangeOrd (Range start1 _) (Range start2 _) = positionOrd start1 start2

lookupInRangeMap :: forall a. Position -> Map Range a -> Maybe a
lookupInRangeMap pos map =
  let
    withinRange :: [(Range, a)] = M.toList $ M.filterWithKey (\k _ -> inRange pos k) map
    -- | Sort them so that the range starting with the latest(!) starting position
    -- comes first.
    withinRangeOrdered = sortBy (\(r1,_) (r2,_) -> rangeOrd r2 r1) withinRange
  in
    case withinRangeOrdered of
      [] -> Nothing
      ((_,ho):_) -> Just ho
