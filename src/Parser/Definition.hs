module Parser.Definition
  ( Parser
  , ParseReader(..)
  , runInteractiveParser
  , runFileParser
  ) where

import Control.Applicative (Alternative)
import Control.Monad.Except
import Control.Monad.Reader ( ReaderT(..), MonadReader )
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text qualified as T
import Data.Void (Void)
import Data.Text (Text)
import Text.Megaparsec

import Syntax.Common ( TVar )
import Errors
import Utils

-------------------------------------------------------------------------------------------
-- Definition of the Parsing Monad
-------------------------------------------------------------------------------------------

data ParseReader = ParseReader { tvars :: Set TVar }

defaultParseReader :: ParseReader
defaultParseReader = ParseReader S.empty

newtype Parser a = Parser { unParser :: ReaderT ParseReader (Parsec Void Text) a }
  deriving (Functor, Applicative, Monad, MonadFail, Alternative, MonadPlus
           , MonadParsec Void Text, MonadReader ParseReader)

-------------------------------------------------------------------------------------------
-- Translating a Parse Error to an Error
-------------------------------------------------------------------------------------------

type MyParseError = ParseErrorBundle Text Void

-- | Compute a position from a given offset and the PosState of the
-- beginning of the file.
getPosFromOffset :: Int ->  PosState Text -> SourcePos
getPosFromOffset offset ps = pstateSourcePos (snd (reachOffset offset ps))

parseErrorToDiag :: PosState Text -> ParseError Text Void -> ParserError
parseErrorToDiag posState err = MkParserError (Loc pos pos) msg
  where
    pos = getPosFromOffset (errorOffset err) posState
    msg = T.pack $ parseErrorTextPretty err


translateError :: MyParseError -> Error
translateError ParseErrorBundle { bundlePosState, bundleErrors } =
  ParserErrorBundle (parseErrorToDiag bundlePosState <$> bundleErrors)

-------------------------------------------------------------------------------------------
-- Running a parser
-------------------------------------------------------------------------------------------

runFileParser :: forall m a. MonadError Error m
              => FilePath -- ^ The Filepath used in Error Messages and Source Locations
              -> Parser a
              -> Text -- ^ The text to be parsed
              -> m a
runFileParser fp p input = case runParser (runReaderT (unParser p) defaultParseReader) fp input of
  Left err -> throwError (translateError err)
  Right x -> pure x

runInteractiveParser :: forall m a.  MonadError Error m
                     => Parser a
                     -> Text -- The text to be parsed
                     -> m a
runInteractiveParser = runFileParser "<interactive>"

