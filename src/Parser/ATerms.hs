module Parser.ATerms ( atermP ) where

import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.CommonTerm
import Syntax.ATerms

acaseP :: NominalStructural -> Parser (ACase ())
acaseP ns = do
  xt <- xtorName ns
  args <- option [] (parens $ freeVarName `sepBy` comma)
  _ <- symbol "=>"
  res <- atermP
  return (MkACase xt ((const ()) <$> args) (atermClosing args res))

fvarP :: Parser (ATerm ())
fvarP = do
  fv <- freeVarName
  return (FVar fv)

ctorP :: NominalStructural -> Parser (ATerm ())
ctorP ns = do
  xt <- xtorName ns
  args <- option [] (parens $ atermP `sepBy` comma)
  return (Ctor xt args)


dtorP :: NominalStructural -> Parser (ATerm ())
dtorP ns = parens $ do
  destructee <- atermP
  _ <- symbol "."
  xt <- xtorName ns
  args <- option [] (parens $ atermP `sepBy` comma)
  return (Dtor xt destructee args)

matchP :: NominalStructural -> Parser (ATerm ())
matchP ns = do
  _ <- symbol "match"
  arg <- atermP
  _ <- symbol "with"
  cases <- braces $ acaseP ns `sepBy` comma
  return (Match arg cases)

comatchP :: NominalStructural -> Parser (ATerm ())
comatchP ns = do
  _ <- symbol "comatch"
  cocases <- braces $ acaseP ns `sepBy` comma
  return (Comatch cocases)

atermP :: Parser (ATerm ())
atermP = matchP Structural <|>
         matchP Nominal <|>
         comatchP Structural <|>
         comatchP Nominal <|>
         ctorP Structural <|>
         ctorP Nominal <|>
         dtorP Structural <|>
         dtorP Nominal <|>
         fvarP

