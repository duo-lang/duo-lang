module Parser.Definition
  ( Parser
  , ParseReader(..)
  , runInteractiveParser
  , runFileParser
  ) where

import Control.Applicative (Alternative)
import Control.Monad.Reader
import Data.Set (Set)
import qualified Data.Set as S
import Data.Void (Void)
import Data.Text (Text)
import qualified Data.Text as T
import Text.Megaparsec

import Syntax.Types
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
-- Running a parser
-------------------------------------------------------------------------------------------

runFileParser :: FilePath -> Parser a -> Text -> Either Error a
runFileParser fp p input = case runParser (runReaderT (unParser p) defaultParseReader) fp input of
  Left err -> Left $ ParseError (T.pack (errorBundlePretty err))
  Right x -> Right x

runInteractiveParser :: Parser a -> Text -> Either Error a
runInteractiveParser p input = runFileParser "<interactive>" p input

