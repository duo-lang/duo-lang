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
import Data.Void
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Syntax.Types
import Utils

data ParseReader = ParseReader
  { rvars :: Set TVar
  , tvars :: Set TVar
  }

defaultParseReader :: ParseReader
defaultParseReader = ParseReader S.empty S.empty

-- A parser that can read values from an environment
newtype Parser a = Parser { unParser :: ReaderT ParseReader (Parsec Void String) a }
  deriving (Functor, Applicative, Monad, MonadFail, Alternative, MonadPlus
           , MonadParsec Void String, MonadReader ParseReader)

runInteractiveParser :: Parser a -> String -> Either Error a
runInteractiveParser p input = runFileParser "<interactive>" p input

runFileParser :: FilePath -> Parser a -> String -> Either Error a
runFileParser fp p input = case runParser (runReaderT (unParser (wrap p)) defaultParseReader) fp input of
  Left err -> Left $ ParseError (errorBundlePretty err)
  Right x -> Right x


wrap :: Parser a -> Parser a
wrap p = lexeme (p <* eof)
  where
    -- TODO: Get rid of these here
    sc :: Parser ()
    sc = L.space space1 (L.skipLineComment "#") (L.skipBlockComment "###" "###")

    lexeme :: Parser a -> Parser a
    lexeme = L.lexeme sc
