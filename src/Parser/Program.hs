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
import Utils (Loc(..))

prdDeclarationP :: Parser (Declaration FreeVarName)
prdDeclarationP = do
  startPos <- getSourcePos
  try prdKwP
  v <- freeVarName
  coloneq
  t <- stermP PrdRep
  endPos <- getSourcePos
  semi
  return (PrdDecl (Loc startPos endPos) v t)

cnsDeclarationP :: Parser (Declaration FreeVarName)
cnsDeclarationP = do
  startPos <- getSourcePos
  try cnsKwP
  v <- freeVarName
  coloneq
  t <- stermP CnsRep
  endPos <- getSourcePos
  semi
  return (CnsDecl (Loc startPos endPos) v t)

cmdDeclarationP :: Parser (Declaration FreeVarName)
cmdDeclarationP = do
  startPos <- getSourcePos
  try cmdKwP
  v <- freeVarName
  coloneq
  t <- commandP
  endPos <- getSourcePos
  semi
  return (CmdDecl (Loc startPos endPos) v t)

defDeclarationP :: Parser (Declaration FreeVarName)
defDeclarationP = do
  startPos <- getSourcePos
  try defKwP
  v <- freeVarName
  coloneq
  t <- atermP
  endPos <- getSourcePos
  semi
  return (DefDecl (Loc startPos endPos) v t)

---------------------------------------------------------------------------------
-- Nominal type declaration parser
---------------------------------------------------------------------------------

dataDeclP :: Parser (Declaration FreeVarName)
dataDeclP = do
  startPos <- getSourcePos
  dataCodata <- dataCodataDeclP
  tn <- typeNameP
  xtors <- braces $ xtorDeclP `sepBy` comma
  endPos <- getSourcePos
  semi
  let decl = NominalDecl
        { data_name = tn
        , data_polarity = dataCodata
        , data_xtors = xtors
        }
  return (DataDecl (Loc startPos endPos) decl)
  where
    dataCodataDeclP :: Parser DataCodata
    dataCodataDeclP = (dataKwP >> return Data) <|> (codataKwP >> return Codata)

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
