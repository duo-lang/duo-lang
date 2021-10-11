module Parser.Definition
  ( Parser
  , ParseReader(..)
  , runInteractiveParser
  , runFileParser
  ) where

import Control.Applicative (Alternative)
import Control.Monad.Reader ( MonadPlus, ReaderT(..), MonadReader )
import Data.Set (Set)
import qualified Data.Set as S
import Data.Void (Void)
import Data.Text (Text)
import Text.Megaparsec
    ( ParseErrorBundle, runParser, Parsec, MonadParsec )

import Syntax.Types ( TVar )

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
-- Running a parser
-------------------------------------------------------------------------------------------

type MyParseError = ParseErrorBundle Text Void

runFileParser :: FilePath -> Parser a -> Text -> Either MyParseError a
runFileParser fp p input = case runParser (runReaderT (unParser p) defaultParseReader) fp input of
  Left err -> Left err
  Right x -> Right x

runInteractiveParser :: Parser a -> Text -> Either MyParseError a
runInteractiveParser = runFileParser "<interactive>"

