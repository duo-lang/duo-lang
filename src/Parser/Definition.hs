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
import Data.Void (Void)
import Text.Megaparsec
import Text.Megaparsec.Debug qualified

import Errors
import Loc ( Loc(..) )

-------------------------------------------------------------------------------------------
-- Definition of the Parsing Monad
-------------------------------------------------------------------------------------------

newtype Parser a = Parser { unParser :: Parsec Void Text a }
  deriving (Functor, Applicative, Monad, MonadFail, Alternative, MonadPlus
           , MonadParsec Void Text)

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

type MyParseError = ParseErrorBundle Text Void

-- | Compute a position from a given offset and the PosState of the
-- beginning of the file.
getPosFromOffset :: Int ->  PosState Text -> SourcePos
getPosFromOffset offset ps = pstateSourcePos (snd (reachOffset offset ps))

parseErrorToDiag :: PosState Text -> ParseError Text Void -> Error
parseErrorToDiag posState err = ErrParser $ SomeParserError (Loc pos pos) msg
  where
    pos = getPosFromOffset (errorOffset err) posState
    msg = T.pack $ parseErrorTextPretty err


translateError :: MyParseError -> NonEmpty Error
translateError ParseErrorBundle { bundlePosState, bundleErrors } =
  parseErrorToDiag bundlePosState <$> bundleErrors

-------------------------------------------------------------------------------------------
-- Running a parser
-------------------------------------------------------------------------------------------

runFileParser :: forall m a. MonadError (NonEmpty Error) m
              => FilePath -- ^ The Filepath used in Error Messages and Source Locations
              -> Parser a
              -> Text -- ^ The text to be parsed
              -> m a
runFileParser fp p input = case runParser (unParser p) fp input of
  Left err -> throwError (translateError err)
  Right x -> pure x

runInteractiveParser :: forall m a.  MonadError (NonEmpty Error) m
                     => Parser a
                     -> Text -- The text to be parsed
                     -> m a
runInteractiveParser = runFileParser "<interactive>"

