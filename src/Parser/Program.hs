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

recoverDeclaration :: Parser (Declaration Parsed) -> Parser (Declaration Parsed)
recoverDeclaration = withRecovery (\err -> registerParseError err >> parseUntilKeywP >> return ParseErrorDecl)

isRecP :: Parser IsRec
isRecP = option NonRecursive (try recKwP >> pure Recursive)

annotP :: PolarityRep pol -> Parser (Maybe (TypeScheme pol))
annotP rep = optional annotP'
  where
    annotP' = try (colon >> typeSchemeP rep)

prdCnsDeclarationP :: PrdCnsRep pc -> Parser (Declaration Parsed)
prdCnsDeclarationP PrdRep = do
  startPos <- getSourcePos
  try (void prdKwP)
  recoverDeclaration $ do
    isRec <- isRecP
    (v, _pos) <- freeVarName
    annot <- annotP PosRep
    _ <- coloneq
    (t,_) <- stermP PrdRep
    endPos <- semi
    return (PrdCnsDecl (Loc startPos endPos) PrdRep isRec v annot t)
prdCnsDeclarationP CnsRep = do
  startPos <- getSourcePos
  try (void cnsKwP)
  recoverDeclaration $ do
    isRec <- isRecP
    (v, _pos) <- freeVarName
    annot <- annotP NegRep
    _ <- coloneq
    (t,_) <- stermP CnsRep
    endPos <- semi
    return (PrdCnsDecl (Loc startPos endPos) CnsRep isRec v annot t)

cmdDeclarationP :: Parser (Declaration Parsed)
cmdDeclarationP = do
  startPos <- getSourcePos
  try (void cmdKwP)
  recoverDeclaration $ do
    (v, _pos) <- freeVarName
    _ <- coloneq
    (t,_) <- commandP
    endPos <- semi
    return (CmdDecl (Loc startPos endPos) v t)

importDeclP :: Parser (Declaration Parsed)
importDeclP = do
  startPos <- getSourcePos
  try (void importKwP)
  (mn, _) <- moduleNameP
  endPos <- semi
  return (ImportDecl (Loc startPos endPos) mn)

setDeclP :: Parser (Declaration Parsed)
setDeclP = do
  startPos <- getSourcePos
  try (void setKwP)
  (txt,_) <- optionP
  endPos <- semi
  return (SetDecl (Loc startPos endPos) txt)
  
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


dataDeclP :: Parser (Declaration Parsed)
dataDeclP = do
  startPos <- getSourcePos
  dataCodata <- dataCodataDeclP
  recoverDeclaration $ do
    (tn, _pos) <- typeNameP
    _ <- colon
    knd <- kindP
    (xtors, _pos) <- braces $ xtorDeclP `sepBy` comma
    endPos <- semi
    let decl = NominalDecl
          { data_name = tn
          , data_polarity = dataCodata
          , data_kind = knd
          , data_xtors = combineXtors xtors
          }
    return (DataDecl (Loc startPos endPos) decl)
    where
      dataCodataDeclP :: Parser DataCodata
      dataCodataDeclP = (dataKwP >> return Data) <|> (codataKwP >> return Codata)



---------------------------------------------------------------------------------
-- Parsing a program
---------------------------------------------------------------------------------

declarationP :: Parser (Declaration Parsed)
declarationP =
  prdCnsDeclarationP PrdRep <|>
  prdCnsDeclarationP CnsRep <|>
  cmdDeclarationP <|>
  importDeclP <|>
  setDeclP <|>
  dataDeclP

programP :: Parser [Declaration Parsed]
programP = do
  sc
  decls <- many declarationP
  eof
  return decls
