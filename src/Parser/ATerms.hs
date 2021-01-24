module Parser.ATerms ( atermP ) where

import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.CommonTerm
import Syntax.ATerms

acaseP :: Parser (ACase ())
acaseP = do
  xt <- xtorName Structural
  args <- parens (freeVarName `sepBy` comma)
  _ <- symbol "=>"
  res <- atermP
  return (MkACase xt ((const ()) <$> args) (atermClosing args res))

fvarP :: Parser (ATerm ())
fvarP = do
  fv <- freeVarName
  return (FVar fv)

ctorP :: Parser (ATerm ())
ctorP = do
  xt <- xtorName Structural
  args <- parens (atermP `sepBy` comma)
  return (Ctor xt args)


dtorP :: Parser (ATerm ())
dtorP = parens $ do
  destructee <- atermP
  _ <- symbol "."
  xt <- xtorName Structural
  args <- parens (atermP `sepBy` comma)
  return (Dtor xt destructee args)

matchP :: Parser (ATerm ())
matchP = do
  _ <- symbol "match"
  arg <- atermP
  _ <- symbol "with"
  cases <- braces $ acaseP `sepBy` comma
  return (Match arg cases)

comatchP :: Parser (ATerm ())
comatchP = do
  _ <- symbol "comatch"
  cocases <- braces $ acaseP `sepBy` comma
  return (Comatch cocases)

atermP :: Parser (ATerm ())
atermP = matchP <|> comatchP <|> fvarP <|> ctorP <|> dtorP

