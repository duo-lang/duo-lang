module Parser.ATerms ( atermP ) where

import Data.List (elemIndex)
import Data.Maybe (isJust, fromJust)
import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.CommonTerm
import Syntax.ATerms

-- TODO, move this to Eval Substitution?
atermClosingRec :: Int -> [FreeVarName] -> ATerm a -> ATerm a
atermClosingRec _ _ bv@(BVar _) = bv
atermClosingRec k args fv@(FVar v) | isJust (v `elemIndex` args) = BVar (k, fromJust (v `elemIndex` args))
                                   | otherwise                   = fv
atermClosingRec k args (Ctor xt args') = Ctor xt (atermClosingRec k args <$> args')
atermClosingRec k args (Dtor xt t args') = Dtor xt (atermClosingRec k args t) (atermClosingRec k args <$> args')
atermClosingRec k args (Match t cases) = Match (atermClosingRec k args t) ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermClosingRec (k + 1) args acase_term }) <$> cases)
atermClosingRec k args (Comatch cocases) = Comatch ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = atermClosingRec (k + 1) args acase_term }) <$> cocases)

atermClosing :: [FreeVarName] -> ATerm () -> ATerm ()
atermClosing = atermClosingRec 0

acaseP :: Parser (ACase ())
acaseP = do
  xt <- xtorName Nominal
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
  xt <- xtorName Nominal
  args <- parens (atermP `sepBy` comma)
  return (Ctor xt args)


dtorP :: Parser (ATerm ())
dtorP = parens $ do
  destructee <- atermP
  _ <- symbol "."
  xt <- xtorName Nominal
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
atermP = fvarP <|> ctorP <|> dtorP <|> matchP <|> comatchP

