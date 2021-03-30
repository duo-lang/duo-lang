module Parser.Program
  ( declarationP
  , programP
  ) where

import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Parser.STerms
import Parser.ATerms
import Parser.Types
import Syntax.Program
import Syntax.STerms
import Syntax.Types

prdDeclarationP :: Parser (Declaration FreeVarName)
prdDeclarationP = do
  (loc, (v,t)) <- withLoc $ do
    _ <- try $ lexeme (symbol "prd")
    v <- freeVarName
    _ <- lexeme (symbol ":=")
    t <- lexeme (stermP PrdRep)
    _ <- symbol ";"
    return (v,t)
  return (PrdDecl loc v t)

cnsDeclarationP :: Parser (Declaration FreeVarName)
cnsDeclarationP = do
  (loc, (v,t)) <- withLoc $ do
    _ <- try $ lexeme (symbol "cns")
    v <- freeVarName
    _ <- lexeme (symbol ":=")
    t <- lexeme (stermP CnsRep)
    _ <- symbol ";"
    return (v,t)
  return (CnsDecl loc v t)

cmdDeclarationP :: Parser (Declaration FreeVarName)
cmdDeclarationP = do
  (loc, (v,t)) <- withLoc $ do
    _ <- try $ lexeme (symbol "cmd")
    v <- freeVarName
    _ <- lexeme (symbol ":=")
    t <- lexeme commandP
    _ <- symbol ";"
    return (v,t)
  return (CmdDecl loc v t)

defDeclarationP :: Parser (Declaration FreeVarName)
defDeclarationP = do
  (loc, (v,t)) <- withLoc $ do
    _ <- try $ (lexeme (symbol "def"))
    v <- freeVarName
    _ <- lexeme (symbol ":=")
    t <- lexeme atermP
    _ <- symbol ";"
    return (v,t)
  return (DefDecl loc v t)

---------------------------------------------------------------------------------
-- Nominal type declaration parser
---------------------------------------------------------------------------------

dataDeclP :: Parser (Declaration FreeVarName)
dataDeclP = do
  (loc, decl) <- withLoc dataDeclP'
  return (DataDecl loc decl)
  where
    dataDeclP' :: Parser DataDecl
    dataDeclP' = do
      dataCodata <- dataCodataDeclP
      tn <- typeNameP
      xtors <- braces $ xtorDeclP `sepBy` comma
      _ <- symbol ";"
      return NominalDecl
        { data_name = tn
        , data_polarity = dataCodata
        , data_xtors = xtors
        }

    dataCodataDeclP :: Parser DataCodata
    dataCodataDeclP = (symbol "data" >> return Data) <|> (symbol "codata" >> return Codata)

    xtorDeclP :: Parser (XtorSig 'Pos)
    xtorDeclP = do
      xt <- xtorName Nominal
      args <- typArgListP PosRep
      return (MkXtorSig xt args)

---------------------------------------------------------------------------------
-- Parsing a program
---------------------------------------------------------------------------------

declarationP :: Parser (Declaration FreeVarName)
declarationP =
  prdDeclarationP <|>
  cnsDeclarationP <|>
  cmdDeclarationP <|>
  defDeclarationP <|>
  dataDeclP

programP :: Parser [Declaration FreeVarName]
programP = do
  sc
  decls <- many declarationP
  eof
  return decls
