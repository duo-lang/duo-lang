module LSP.MegaparsecToLSP where

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

lookupPos :: Position -> Loc -> Bool 
lookupPos (Position l _) (Loc begin end) =
  let
    (Position l1 _) = posToPosition  begin
    (Position l2 _) = posToPosition end 
  in
    l1 <= l && l <= l2