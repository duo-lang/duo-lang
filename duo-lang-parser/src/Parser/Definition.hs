module Parser.Definition
  ( Parser
  , runInteractiveParser
  , runFileParser
  , dbg
  , parseTst
  ) where

import Control.Applicative (Alternative)
import Control.Monad.Except
import Data.List.NonEmpty ( NonEmpty )
import Data.Text qualified as T
import Data.Text (Text)
import Text.Megaparsec
import Text.Megaparsec.Debug qualified

import Errors.Parser
import Loc ( Loc(..) )

-------------------------------------------------------------------------------------------
-- Definition of the Parsing Monad
-------------------------------------------------------------------------------------------

type FancyParseError = Text
instance ShowErrorComponent FancyParseError where
    showErrorComponent = T.unpack
    errorComponentLen = T.length

newtype Parser a = Parser { unParser :: Parsec FancyParseError Text a }
  deriving newtype (Functor, Applicative, Monad, MonadFail, Alternative, MonadPlus
                   , MonadParsec FancyParseError Text)

-------------------------------------------------------------------------------------------
-- Debugging Support 
-------------------------------------------------------------------------------------------

dbg :: Show a => String   -> Parser a    -> Parser a
dbg txt (Parser p) = Parser $ Text.Megaparsec.Debug.dbg txt p

parseTst :: Show a => Parser a -> Text -> IO ()
parseTst (Parser p) = Text.Megaparsec.parseTest p

-------------------------------------------------------------------------------------------
-- Translating a Parse Error to an Error
-------------------------------------------------------------------------------------------

type MyParseError = ParseErrorBundle Text FancyParseError

-- | Compute a position from a given offset and the PosState of the
-- beginning of the file.
getPosFromOffset :: Int ->  PosState Text -> SourcePos
getPosFromOffset offset ps = pstateSourcePos (snd (reachOffset offset ps))

parseErrorToDiag :: PosState Text -> ParseError Text FancyParseError -> ParserError
parseErrorToDiag posState err = SomeParserError (Loc pos pos) msg
  where
    pos = getPosFromOffset (errorOffset err) posState
    msg = T.pack $ parseErrorTextPretty err


translateError :: MyParseError -> NonEmpty ParserError
translateError err = parseErrorToDiag err.bundlePosState <$> err.bundleErrors

-------------------------------------------------------------------------------------------
-- Running a parser
-------------------------------------------------------------------------------------------

runFileParser :: forall m a e. MonadError (NonEmpty e) m
              => FilePath -- ^ The Filepath used in Error Messages and Source Locations
              -> Parser a
              -> Text -- ^ The text to be parsed
              -> (ParserError -> e) -- ^ The function used to embed the error.
              -> m a
runFileParser fp p input f = case runParser p.unParser fp input of
  Left err -> throwError (f <$> (translateError err))
  Right x -> pure x

runInteractiveParser :: forall m a e.  MonadError (NonEmpty e) m
                     => Parser a
                     -> Text -- The text to be parsed
                     -> (ParserError -> e)
                     -> m a
runInteractiveParser p input f = runFileParser "<interactive>" p input f

