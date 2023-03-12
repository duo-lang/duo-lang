{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
module Parser.Lexer
  ( -- Space Consumer and Comments
    sc
  , scne
  , docCommentP
    -- Literals
  , natP
  , charP
  , stringP
  , intP
  , uintP
  , floatP
    -- Identifier
  , lowerCaseIdL
  , upperCaseIdL
  , allCaseIdL
    -- Operators
  , operatorP
  -- Keywords
  , Keyword(..)
  , keywordP
  -- Symbols
  , Symbol(..)
  , symbolP
  -- Parens
  , anglesP
  , parensP
  , bracketsP
  , bracesP
  -- Other
  , checkTick
  , parseUntilKeywP
  ) where

import Data.Foldable (asum)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Char (isAlphaNum, isSpace, isPunctuation)
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L
import Text.Megaparsec.Char.Lexer (decimal, signed, float)
import Control.Monad (void)

import Parser.Definition
import Syntax.CST.Names
import Syntax.CST.Terms qualified as CST



-------------------------------------------------------------------------------------------
-- General lexing conventions around space consumption and source code locations:
--
-- Every lexer and parser is responsible for consuming it's trailing whitespace using the
-- space consumer `sc`.
-- In addition, every parser returns the source position of the end of the last parsed
-- non-whitespace token.
--
-- Example:
-- A parser for number literals:
--
-- (This source position is returned)
--            ||
--            \/
--    123456789          foo
--    ^^^^^^^^^^^^^^^^^^^
--      (this is parsed)
--
-------------------------------------------------------------------------------------------

-- | Parses comments starting with "--", but not doccomments starting with "-- |"
commentP :: Parser ()
commentP = do
  try $ do
    _ <- string "--"
    notFollowedBy (string " |")
  _ <- takeWhileP (Just "character") (/= '\n')
  pure ()

-- | Parses a doc comment starting with "-- |" until the end of the line, and does
-- not consume the trailing "\n"
docCommentP :: Parser (DocComment, SourcePos)
docCommentP = do
  _ <- string "-- |"
  comment <- takeWhileP (Just "character") (/= '\n')
  endPos <- getSourcePos
  pure (MkDocComment comment, endPos)

-- | The space consumer. Consumes Comments but not doc comments.
sc :: Parser ()
sc = L.space space1 commentP empty

-- Nonempty space
scne :: Parser ()
scne = space1 >> sc

-------------------------------------------------------------------------------------------
-- Helper functions
-------------------------------------------------------------------------------------------

natP :: Parser (Int, SourcePos)
natP = do
  numStr <- some numberChar
  endPos <- getSourcePos
  return (read numStr, endPos)

scharP :: Parser Char
scharP = satisfy isSChar <?> "string character"
  where
    isSChar c = isAlphaNum c || isSpace c || (isPunctuation c && c /= '"' && c /= '\'')

charP :: Parser (Char, SourcePos)
charP = do
  symbolP SymSingleQuote
  ch <- scharP
  symbolP SymSingleQuote
  pos <- getSourcePos
  pure (ch, pos)

stringP :: Parser (String, SourcePos)
stringP = do
  symbolP SymDoubleQuote
  s <- manyTill scharP (symbolP SymDoubleQuote)
  pos <- getSourcePos
  return (s, pos)

uintP :: Parser (Integer, SourcePos)
uintP = do
  pos <- getSourcePos
  i <- decimal
  pure (i, pos)

intP :: Parser (Integer, SourcePos)
intP = do
  pos <- getSourcePos
  i <- signed space decimal
  pure (i, pos)

floatP :: Parser (Double, SourcePos)
floatP = do
  pos <- getSourcePos
  f <- signed space float
  pure (f, pos)

-------------------------------------------------------------------------------------------
-- Identifier
-------------------------------------------------------------------------------------------

-- | Parses a lower case identifer, eg `foo`.
-- Does not parse trailing whitespace.
lowerCaseIdL :: Parser (Text, SourcePos)
lowerCaseIdL = do
  name <- T.cons <$> lowerChar <*> (T.pack <$> many (alphaNumChar <|> char '_'))
  checkReserved name
  pos <- getSourcePos
  pure (name, pos)

-- | Parses an upper case identifier, e.g. `Foo`.
-- Does not parse trailing whitespace.
upperCaseIdL :: Parser (Text, SourcePos)
upperCaseIdL = do
  name <- T.cons <$> upperChar <*> (T.pack <$> many (alphaNumChar <|> char '_'))
  checkReserved name
  pos <- getSourcePos
  pure (name, pos)

-- | Parses an upper or lower case identifier, e.g. `Foo` or `foo`.
-- Does not parse trailing whitespace.
allCaseIdL :: Parser (Text, SourcePos)
allCaseIdL = do
  name <- T.cons <$> alphaNumChar <*> (T.pack <$> many (alphaNumChar <|> char '_'))
  checkReserved name
  pos <- getSourcePos
  pure (name, pos)

-------------------------------------------------------------------------------------------
-- Operators
-------------------------------------------------------------------------------------------

operatorP :: Parser (Text, SourcePos)
operatorP = backtickOperator <|> funOperator <|> otherOperator
  where
    -- We have to treat the function arrow specially, since we want to allow it
    -- as an operator, but it is also a reserved symbol.
    funOperator = do
      symbolP SymSimpleRightArrow
      pos <- getSourcePos
      pure ("->",pos)
    otherOperator = do
      name <- T.pack <$> many (symbolChar <|> punctuationChar)
      checkReservedOp name
      pos <- getSourcePos
      pure (name, pos)
    backtickOperator = do
      symbolP SymBacktick
      name <- T.pack <$> many alphaNumChar
      symbolP SymBacktick
      pos <- getSourcePos
      pure ("`" <> name <> "`", pos)

---

checkTick :: CST.NominalStructural -> Parser ()
checkTick CST.Nominal = return ()
checkTick CST.Refinement = return ()
checkTick CST.Structural = void (symbolP SymSingleQuote)

-------------------------------------------------------------------------------------------
-- Keywords
-------------------------------------------------------------------------------------------

data Keyword where
  -- Term Keywords
  KwCase        :: Keyword
  KwCocase      :: Keyword
  KwOf          :: Keyword
  KwMu          :: Keyword
  -- Type and Kind Keywords
  KwForall      :: Keyword
  KwRec         :: Keyword
  KwTop         :: Keyword
  KwBot         :: Keyword
  KwCBV         :: Keyword
  KwCBN         :: Keyword
  KwI64         :: Keyword
  KwF64         :: Keyword
  KwChar        :: Keyword
  KwString      :: Keyword
  KwF64Rep      :: Keyword
  KwI64Rep      :: Keyword
  KwCharRep     :: Keyword
  KwStringRep   :: Keyword
  KwOperator    :: Keyword
  KwAt          :: Keyword
  KwLeftAssoc   :: Keyword
  KwRightAssoc  :: Keyword
  -- Declaration Keywords
  KwType        :: Keyword
  KwRefinement  :: Keyword
  KwConstructor :: Keyword
  KwDestructor  :: Keyword
  KwDef         :: Keyword
  KwData        :: Keyword
  KwCodata      :: Keyword
  KwSet         :: Keyword
  KwImport      :: Keyword
  KwModule      :: Keyword
  KwPrd         :: Keyword
  KwCns         :: Keyword
  KwCmd         :: Keyword
  KwReturn      :: Keyword
  KwClass       :: Keyword
  KwInstance    :: Keyword

  deriving (Eq, Ord, Enum, Bounded)

instance Show Keyword where
  -- Term Keywords
  show KwCase        = "case"
  show KwCocase      = "cocase"
  show KwOf          = "of"
  show KwMu          = "mu"
  -- Type and Kind Keywords
  show KwForall      = "forall"
  show KwRec         = "rec"
  show KwTop         = "Top"
  show KwBot         = "Bot"
  show KwCBV         = "CBV"
  show KwCBN         = "CBN"
  show KwI64         = "#I64"
  show KwF64         = "#F64"
  show KwChar        = "#Char"
  show KwString      = "#String"
  show KwF64Rep      = "F64Rep"
  show KwI64Rep      = "I64Rep"
  show KwCharRep     = "CharRep"
  show KwStringRep   = "StringRep"
  show KwOperator    = "operator"
  show KwAt          = "at"
  show KwLeftAssoc   = "leftassoc"
  show KwRightAssoc  = "rightassoc"
  -- Declaration Keywords
  show KwType        = "type"
  show KwRefinement  = "refinement"
  show KwConstructor = "constructor"
  show KwDestructor  = "destructor"
  show KwDef         = "def"
  show KwData        = "data"
  show KwCodata      = "codata"
  show KwSet         = "set"
  show KwImport      = "import"
  show KwModule      = "module"
  show KwPrd         = "prd"
  show KwCns         = "cns"
  show KwCmd         = "cmd"
  show KwReturn      = "return"
  show KwClass       = "class"
  show KwInstance    = "instance"


-- | These keywords start a new declaration at the toplevel and
--   are used to restart parsing after a parse error has been
--   encountered.
isDeclarationKw :: Keyword -> Bool
-- Term Keywords
isDeclarationKw KwCase        = False
isDeclarationKw KwCocase      = False
isDeclarationKw KwOf          = False
isDeclarationKw KwMu          = False
-- Type and Kind Keywords
isDeclarationKw KwForall      = False
isDeclarationKw KwRec         = False
isDeclarationKw KwTop         = False
isDeclarationKw KwBot         = False
isDeclarationKw KwCBV         = False
isDeclarationKw KwCBN         = False
isDeclarationKw KwI64         = False
isDeclarationKw KwF64         = False
isDeclarationKw KwChar        = False
isDeclarationKw KwString      = False
isDeclarationKw KwF64Rep      = False
isDeclarationKw KwI64Rep      = False
isDeclarationKw KwCharRep     = False
isDeclarationKw KwStringRep   = False
isDeclarationKw KwOperator    = False
isDeclarationKw KwAt          = False
isDeclarationKw KwLeftAssoc   = False
isDeclarationKw KwRightAssoc  = False
-- Declaration Keywords
isDeclarationKw KwType        = True
isDeclarationKw KwRefinement  = True
isDeclarationKw KwConstructor = True
isDeclarationKw KwDestructor  = True
isDeclarationKw KwDef         = True
isDeclarationKw KwData        = True
isDeclarationKw KwCodata      = True
isDeclarationKw KwSet         = True
isDeclarationKw KwImport      = True
isDeclarationKw KwModule      = True
isDeclarationKw KwPrd         = False
isDeclarationKw KwCns         = False
isDeclarationKw KwCmd         = False
isDeclarationKw KwReturn      = False
isDeclarationKw KwClass       = True
isDeclarationKw KwInstance    = True


-- | All keywords of the language
keywords :: [Keyword]
keywords = enumFromTo minBound maxBound

-- | All keywords which start toplevel declarations
declKeywords :: [Keyword]
declKeywords = filter isDeclarationKw keywords

-- | A parser which parses a keyword
keywordP :: Keyword -> Parser SourcePos
keywordP kw = do
  _ <- string (T.pack (show kw)) <* notFollowedBy alphaNumChar
  getSourcePos

parseUntilKeywP :: Parser ()
parseUntilKeywP = do
  let endP = asum ([keywordP kw | kw <- declKeywords] ++ [eof >> getSourcePos, snd <$> docCommentP])
  _ <- manyTill anySingle (lookAhead endP)
  return ()

-- Check if the string is in the list of reserved keywords.
-- Reserved keywords cannot be used as identifiers.
checkReserved :: Text -> Parser ()
checkReserved str | str `elem` (T.pack . show <$> keywords) = fail . T.unpack $ "Keyword " <> str <> " cannot be used as an identifier."
                  | otherwise = return ()

-------------------------------------------------------------------------------------------
-- Symbols
-------------------------------------------------------------------------------------------

data Symbol where
  SymComma            :: Symbol
  SymDot              :: Symbol
  SymSemi             :: Symbol
  SymDoubleSemi       :: Symbol
  SymColon            :: Symbol
  SymPipe             :: Symbol
  SymSingleQuote      :: Symbol
  SymDoubleQuote      :: Symbol
  SymBackslash        :: Symbol
  SymColoneq          :: Symbol
  SymDoubleRightArrow :: Symbol
  SymDoubleCoRightArrow :: Symbol
  SymSimpleRightArrow :: Symbol
  SymCommand          :: Symbol
  SymSubtype          :: Symbol
  SymImplicit         :: Symbol
  SymWildcard         :: Symbol
  SymPlus             :: Symbol
  SymMinus            :: Symbol
  SymHash             :: Symbol
  SymBacktick         :: Symbol
  SymForallUnicode    :: Symbol
  -- Lattice Types
  SymTopUnicode       :: Symbol
  SymBotUnicode       :: Symbol
  SymUnion            :: Symbol
  SymUnionUnicode     :: Symbol
  SymInter            :: Symbol
  SymInterUnicode     :: Symbol
  -- Parens Symbols
  SymParenLeft        :: Symbol
  SymParenRight       :: Symbol
  SymBraceLeft        :: Symbol
  SymBraceRight       :: Symbol
  SymBracketLeft      :: Symbol
  SymBracketRight     :: Symbol
  SymAngleLeft        :: Symbol
  SymAngleRight       :: Symbol
  deriving (Eq, Ord, Enum, Bounded)

instance Show Symbol where
  show SymComma            = ","
  show SymDot              = "."
  show SymSemi             = ";"
  show SymDoubleSemi       = ";;"
  show SymColon            = ":"
  show SymPipe             = "|"
  show SymSingleQuote      = "'"
  show SymDoubleQuote      = "\""
  show SymBackslash        = "\\"
  show SymColoneq          = ":="
  show SymDoubleRightArrow = "=>"
  show SymDoubleCoRightArrow = "=<"
  show SymSimpleRightArrow = "->"
  show SymCommand          = ">>"

  show SymSubtype          = "<:"
  show SymImplicit         = "*"
  show SymWildcard         = "_"
  show SymPlus             = "+"
  show SymMinus            = "-"
  show SymHash             = "#"
  show SymBacktick         = "`"
  show SymForallUnicode    = "∀"
  -- Lattice types
  show SymTopUnicode       = "⊤"
  show SymBotUnicode       = "⊥"
  show SymUnion            = "\\/"
  show SymUnionUnicode     = "∨"
  show SymInter            = "/\\"
  show SymInterUnicode     = "∧"
  -- Parens Symbols
  show SymParenLeft        = "("
  show SymParenRight       = ")"
  show SymBraceLeft        = "{"
  show SymBraceRight       = "}"
  show SymBracketLeft      = "["
  show SymBracketRight     = "]"
  show SymAngleLeft        = "<"
  show SymAngleRight       = ">"

-- | symbolP does NOT consume trailing whitespace.
symbolP :: Symbol -> Parser ()
symbolP sym = do
  _ <- string (T.pack (show sym))
  pure ()

operators :: [Symbol]
operators = enumFromTo minBound maxBound

-- Check if the string is in the list of reserved operators.
-- Reserved operators cannot be used as custom operators
checkReservedOp :: Text -> Parser ()
checkReservedOp str | str == "-<" = pure () -- Special case for cofunctions =D
checkReservedOp str | any (\op -> op `T.isInfixOf` str) (T.pack . show <$> operators) = fail . T.unpack $ "Operator " <> str <> " cannot be used as a custom operator."
                    | otherwise = return ()

-------------------------------------------------------------------------------------------
-- Parens
-------------------------------------------------------------------------------------------

-- | The parser provided to `parens` must parse its own trailing whitespace.
-- The `parens` parser doesn't parse trailing whitespace.
parensP :: Parser a -> Parser (a, SourcePos)
parensP parser = do
  symbolP SymParenLeft
  sc
  res <- parser
  symbolP SymParenRight
  endPos <- getSourcePos
  pure (res, endPos)

-- | The parser provided to `braces` must parse its own trailing whitespace.
-- The `braces` parser doesn't parse trailing whitespace.
bracesP :: Parser a -> Parser (a, SourcePos)
bracesP parser = do
  symbolP SymBraceLeft
  sc
  res <- parser
  symbolP SymBraceRight
  endPos <- getSourcePos
  pure (res, endPos)

-- | The parser provided to `brackets` must parse its own trailing whitespace.
-- The `brackets` parser doesn't parse trailing whitespace.
bracketsP :: Parser a -> Parser (a, SourcePos)
bracketsP parser = do
  symbolP SymBracketLeft
  sc
  res <- parser
  symbolP SymBracketRight
  endPos <- getSourcePos
  pure (res, endPos)

-- | The parser provided to `angles` must parse its own trailing whitespace.
-- The `angles` parser doesn't parse trailing whitespace.
anglesP :: Parser a -> Parser (a, SourcePos)
anglesP parser = do
  symbolP SymAngleLeft
  sc
  res <- parser
  symbolP SymAngleRight
  endPos <- getSourcePos
  pure (res, endPos)
