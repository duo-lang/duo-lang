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
import Text.Megaparsec

import Syntax.Types
import Utils

-------------------------------------------------------------------------------------------
-- Definition of the Parsing Monad
-------------------------------------------------------------------------------------------

data ParseReader = ParseReader
  { rvars :: Set TVar
  , tvars :: Set TVar
  }

defaultParseReader :: ParseReader
defaultParseReader = ParseReader S.empty S.empty

newtype Parser a = Parser { unParser :: ReaderT ParseReader (Parsec Void String) a }
  deriving (Functor, Applicative, Monad, MonadFail, Alternative, MonadPlus
           , MonadParsec Void String, MonadReader ParseReader)

-------------------------------------------------------------------------------------------
-- Running a parser
-------------------------------------------------------------------------------------------

runFileParser :: FilePath -> Parser a -> String -> Either Error a
runFileParser fp p input = case runParser (runReaderT (unParser p) defaultParseReader) fp input of
  Left err -> Left $ ParseError (errorBundlePretty err)
  Right x -> Right x

runInteractiveParser :: Parser a -> String -> Either Error a
runInteractiveParser p input = runFileParser "<interactive>" p input

