{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Avoid lambda using `infix`" #-}
module Parser.Lexer
  ( -- Space Consumer and Comments
    sc
  , docCommentP
    -- Literals
  , natP
  , charP
  , stringP
  , intP
  , uintP
  , floatP
    -- Identifier
  , lowerCaseId
  , upperCaseId
  , operatorP
  , allCaseId
  -- Keywords
  , Keyword(..)
  , keywordP
  -- Symbols
  , Symbol(..)
  , symbolP
  -- Parens
  , angles
  , parens
  , brackets
  , braces
  -- Other
  , primOpKeywordP
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

import Parser.Definition
import Syntax.Common.Names
import Syntax.Common.Primitives
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

-------------------------------------------------------------------------------------------
-- Helper functions
-------------------------------------------------------------------------------------------

natP :: Parser (Int, SourcePos)
natP = do
  numStr <- some numberChar
  endPos <- getSourcePos
  sc
  return (read numStr, endPos)

scharP :: Parser Char
scharP = satisfy isSChar <?> "string character"
  where
    isSChar c = isAlphaNum c || isSpace c || (isPunctuation c && c /= '"' && c /= '\'')

charP :: Parser (Char, SourcePos)
charP = do
  (ch, pos) <- betweenP (symbolP SymSingleQuote) (symbolP SymSingleQuote) scharP
  return (ch, pos)

stringP :: Parser (String, SourcePos)
stringP = do
  s <- symbolP SymDoubleQuote >> manyTill scharP (symbolP SymDoubleQuote)
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
-- Names
-------------------------------------------------------------------------------------------

lowerCaseId :: Parser (Text, SourcePos)
lowerCaseId = do
  name <- T.cons <$> lowerChar <*> (T.pack <$> many alphaNumChar)
  checkReserved name
  pos <- getSourcePos
  sc
  pure (name, pos)

upperCaseId :: Parser (Text, SourcePos)
upperCaseId = do
  name <- T.cons <$> upperChar <*> (T.pack <$> many alphaNumChar)
  checkReserved name
  pos <- getSourcePos
  sc
  pure (name, pos)

allCaseId :: Parser (Text, SourcePos)
allCaseId = do
  name <- T.pack <$> many alphaNumChar
  checkReserved name
  pos <- getSourcePos
  sc
  pure (name, pos)

operatorP :: Parser (Text, SourcePos)
operatorP = funOperator <|> otherOperator
  where
    -- We have to treat the function arrow specially, since we want to allow it
    -- as an operator, but it is also a reserved symbol.
    funOperator = symbolP SymSimpleRightArrow >>= \pos -> pure ("->",pos)
    otherOperator = do
      name <- T.pack <$> many (symbolChar <|> punctuationChar)
      checkReservedOp name
      pos <- getSourcePos
      sc
      pure (name, pos)

---

checkTick :: CST.NominalStructural -> Parser ()
checkTick CST.Nominal = return ()
checkTick CST.Refinement = return ()
checkTick CST.Structural = () <$ symbolP SymSingleQuote

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
  -- Command Keywords
  KwExitSuccess :: Keyword
  KwExitFailure :: Keyword
  KwPrint       :: Keyword
  KwRead        :: Keyword
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
  -- Command Keywords
  show KwExitSuccess = "ExitSuccess"
  show KwExitFailure = "ExitFailure"
  show KwPrint       = "Print"
  show KwRead        = "Read"
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
-- Command Keywords
isDeclarationKw KwExitSuccess = False
isDeclarationKw KwExitFailure = False
isDeclarationKw KwPrint       = False
isDeclarationKw KwRead        = False
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
  endPos <- getSourcePos
  sc
  return endPos

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

primOpKeywordP :: PrimitiveType -> PrimitiveOp -> Parser (PrimitiveType, PrimitiveOp, SourcePos)
primOpKeywordP pt op = do
  _ <- string (T.pack (primOpKeyword op ++ primTypeKeyword pt))
  endPos <- getSourcePos
  sc
  pure (pt, op, endPos)

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
  SymUnion            :: Symbol
  SymIntersection     :: Symbol
  SymSubtype          :: Symbol
  SymImplicit         :: Symbol
  SymWildcard         :: Symbol
  SymPlus             :: Symbol
  SymMinus            :: Symbol
  SymHash             :: Symbol
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
  show SymUnion            = "\\/"
  show SymIntersection     = "/\\"
  show SymSubtype          = "<:"
  show SymImplicit         = "*"
  show SymWildcard         = "_"
  show SymPlus             = "+"
  show SymMinus            = "-"
  show SymHash             = "#"
  -- Parens Symbols
  show SymParenLeft        = "("
  show SymParenRight       = ")"
  show SymBraceLeft        = "{"
  show SymBraceRight       = "}"
  show SymBracketLeft      = "["
  show SymBracketRight     = "]"
  show SymAngleLeft        = "<"
  show SymAngleRight       = ">"

symbolP :: Symbol -> Parser SourcePos
symbolP sym = do
  _ <- string (T.pack (show sym))
  endPos <- getSourcePos
  sc
  return endPos

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

betweenP :: Show a => Parser SourcePos -> Parser SourcePos -> Parser a -> Parser (a, SourcePos)
betweenP open close middle = do
  _ <- open
  res <- middle
  endPos <- close
  pure (res, endPos)

parens, braces, brackets, angles :: Show a => Parser a -> Parser (a, SourcePos)
parens    = betweenP (symbolP SymParenLeft)   (symbolP SymParenRight)
braces    = betweenP (symbolP SymBraceLeft)   (symbolP SymBraceRight)
brackets  = betweenP (symbolP SymBracketLeft) (symbolP SymBracketRight)
angles    = betweenP (symbolP SymAngleLeft)   (symbolP SymAngleRight)
