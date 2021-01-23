module Parser.Definition where

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Control.Monad.Reader
import Data.Set (Set)
import qualified Data.Set as S
import Data.Void

import Syntax.Types
import Syntax.Program
import Utils

data ParseReader = ParseReader
  { rvars :: Set TVar
  , tvars :: Set TVar
  , parseEnv :: Syntax.Program.Environment
  }

defaultParseReader :: Syntax.Program.Environment -> ParseReader
defaultParseReader env = ParseReader S.empty S.empty env

-- A parser that can read values from an environment
type Parser a = ReaderT ParseReader (Parsec Void String) a

runEnvParser :: Parser a -> Syntax.Program.Environment -> String -> Either Error a
runEnvParser p env input = case runParser (runReaderT (lexeme (p <* eof)) (defaultParseReader env)) "<interactive>" input of
  Left err -> Left $ ParseError (errorBundlePretty err)
  Right x -> Right x
  where
    -- TODO: Get rid of these here
    sc :: (MonadParsec Void String m) => m ()
    sc = L.space space1 (L.skipLineComment "#") (L.skipBlockComment "###" "###")

    lexeme :: (MonadParsec Void String m) => m a -> m a
    lexeme = L.lexeme sc
