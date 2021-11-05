module LSP.MegaparsecToLSP where

import Data.Text (Text)
import Data.Text qualified as T
import Data.Void (Void)
import Data.List.NonEmpty qualified as NE
import Text.Megaparsec
    ( PosState(pstateSourcePos),
      SourcePos(SourcePos),
      errorOffset,
      ParseErrorBundle(..),
      TraversableStream(reachOffset),
      unPos, ParseError, parseErrorTextPretty )
import Utils ( Loc(..) )
import Language.LSP.Types
    ( Position(..),
      Range(..),
      Diagnostic(..),
      DiagnosticSeverity(DsError) )

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

-- | Compute a position from a given offset and the PosState of the
-- beginning of the file.
getPosFromOffset :: Int ->  PosState Text -> Position
getPosFromOffset offset ps =
  let
    ps' = snd (reachOffset offset ps)
  in
    posToPosition (pstateSourcePos ps')

parseErrorToDiag :: PosState Text -> ParseError Text Void -> Diagnostic 
parseErrorToDiag posState err = do
    let offset = errorOffset err
    let pos = getPosFromOffset offset posState
    let rng = Range pos pos
    let msg = T.pack $ parseErrorTextPretty err
    Diagnostic { _range = rng
               , _severity = Just DsError
               , _code = Nothing
               , _source = Nothing
               , _message = msg
               , _tags = Nothing
               , _relatedInformation = Nothing
               }

parseErrorBundleToDiag :: ParseErrorBundle Text Void -> [Diagnostic]
parseErrorBundleToDiag ParseErrorBundle { bundlePosState, bundleErrors } =
    NE.toList  $ parseErrorToDiag bundlePosState <$> bundleErrors

lookupPos :: Position -> Loc -> Bool 
lookupPos (Position l _) (Loc begin end) =
  let
    (Position l1 _) = posToPosition  begin
    (Position l2 _) = posToPosition end 
  in
    l1 <= l && l <= l2