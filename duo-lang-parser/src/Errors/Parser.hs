module Errors.Parser where

import Control.Monad.Except
import Data.List.NonEmpty ( NonEmpty )
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text qualified as T

import Syntax.CST.Names
import Syntax.CST.Types (PrdCns)
import Loc

----------------------------------------------------------------------------------
-- Errors emitted during parsing
----------------------------------------------------------------------------------

data ParserError where
  SomeParserError :: Loc -> Text -> ParserError

deriving instance Show ParserError

instance HasLoc ParserError where
  getLoc (SomeParserError loc _) =
    loc

instance AttachLoc ParserError where
  attachLoc loc (SomeParserError _ msg) =
    SomeParserError loc msg
