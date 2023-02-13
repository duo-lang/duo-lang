module Errors.Parser where

import Data.Text (Text)

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
