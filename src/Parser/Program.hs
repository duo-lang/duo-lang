module Parser.Program
  ( declarationP
  , programP
  ) where

import Control.Monad (void)
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

isRecP :: Parser IsRec
isRecP = option NonRecursive (try recKwP >> pure Recursive)


prdDeclarationP :: Parser (Declaration FreeVarName Loc)
prdDeclarationP = do
  startPos <- getSourcePos
  try (void prdKwP)
  isRec <- isRecP
  (v, _pos) <- freeVarName
  _ <- coloneq
  (t,_) <- stermP PrdRep
  endPos <- semi
  return (PrdDecl isRec (Loc startPos endPos) v t)

cnsDeclarationP :: Parser (Declaration FreeVarName Loc)
cnsDeclarationP = do
  startPos <- getSourcePos
  try (void cnsKwP)
  isRec <- isRecP
  (v, _pos) <- freeVarName
  _ <- coloneq
  (t,_) <- stermP CnsRep
  endPos <- semi
  return (CnsDecl isRec (Loc startPos endPos) v t)

cmdDeclarationP :: Parser (Declaration FreeVarName Loc)
cmdDeclarationP = do
  startPos <- getSourcePos
  try (void cmdKwP)
  (v, _pos) <- freeVarName
  _ <- coloneq
  (t,_) <- commandP
  endPos <- semi
  return (CmdDecl (Loc startPos endPos) v t)

defDeclarationP :: Parser (Declaration FreeVarName Loc)
defDeclarationP = do
  startPos <- getSourcePos
  try (void defKwP)
  isRec <- isRecP
  (v, _pos) <- freeVarName
  _ <- coloneq
  (t, _pos) <- atermP
  endPos <- semi
  return (DefDecl isRec (Loc startPos endPos) v t)

---------------------------------------------------------------------------------
-- Nominal type declaration parser
---------------------------------------------------------------------------------

xtorDeclP :: Parser (XtorName, [Invariant], [Invariant])
xtorDeclP = do
  (xt, _pos) <- xtorName Nominal
  prdArgs <- option [] (fst <$> (parens   $ invariantP `sepBy` comma))
  cnsArgs <- option [] (fst <$> (brackets $ invariantP `sepBy` comma))
  return (xt,prdArgs, cnsArgs)

combineXtors :: [(XtorName, [Invariant], [Invariant])] -> (forall pol. PolarityRep pol -> [XtorSig pol])
combineXtors [] = \_rep -> []
combineXtors ((xt, prdArgs, cnsArgs):rest) = \rep -> MkXtorSig
  xt (MkTypArgs ((\x -> (unInvariant x) rep) <$> prdArgs)
       ((\x -> (unInvariant x) (flipPolarityRep rep)) <$> cnsArgs )) : combineXtors rest rep


dataDeclP :: Parser (Declaration FreeVarName Loc)
dataDeclP = do
  startPos <- getSourcePos
  dataCodata <- dataCodataDeclP
  (tn, _pos) <- typeNameP
  (xtors, _pos) <- braces $ xtorDeclP `sepBy` comma
  endPos <- semi
  let decl = NominalDecl
        { data_name = tn
        , data_polarity = dataCodata
        , data_xtors = combineXtors xtors
        }
  return (DataDecl (Loc startPos endPos) decl)
  where
    dataCodataDeclP :: Parser DataCodata
    dataCodataDeclP = (dataKwP >> return Data) <|> (codataKwP >> return Codata)



---------------------------------------------------------------------------------
-- Parsing a program
---------------------------------------------------------------------------------

declarationP :: Parser (Declaration FreeVarName Loc)
declarationP =
  prdDeclarationP <|>
  cnsDeclarationP <|>
  cmdDeclarationP <|>
  defDeclarationP <|>
  dataDeclP

programP :: Parser [Declaration FreeVarName Loc]
programP = do
  sc
  decls <- many declarationP
  eof
  return decls
