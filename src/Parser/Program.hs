module Parser.Program
  ( declarationP
  , programP
  ) where

import Control.Monad (void)
import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Parser.Terms
import Parser.Types
import Syntax.CST.Program
import Syntax.CST.Types
import Syntax.CommonTerm
import Syntax.AST.Types (DataCodata(..))
import Syntax.Lowering.Types (Assoc(..),Precedence(..))
import Utils

recoverDeclaration :: Parser Declaration -> Parser Declaration
recoverDeclaration = withRecovery (\err -> registerParseError err >> parseUntilKeywP >> return ParseErrorDecl)

isRecP :: Parser IsRec
isRecP = option NonRecursive (try recKwP >> pure Recursive)

annotP :: Parser (Maybe TypeScheme)
annotP = optional (try (notFollowedBy coloneq *> colon) >> typeSchemeP)

prdCnsDeclarationP :: PrdCns -> Parser Declaration
prdCnsDeclarationP pc = do
  startPos <- getSourcePos
  try (void (case pc of Prd -> prdKwP; Cns -> cnsKwP))
  recoverDeclaration $ do
    isRec <- isRecP
    (v, _pos) <- freeVarName
    annot <- annotP
    _ <- coloneq
    (tm,_) <- termP
    endPos <- semi
    pure (PrdCnsDecl (Loc startPos endPos) pc isRec v annot tm)

cmdDeclarationP :: Parser Declaration
cmdDeclarationP = do
  startPos <- getSourcePos
  try (void cmdKwP)
  recoverDeclaration $ do
    (v, _pos) <- freeVarName
    _ <- coloneq
    (cmd,_) <- commandP
    endPos <- semi
    pure (CmdDecl (Loc startPos endPos) v cmd)

importDeclP :: Parser Declaration
importDeclP = do
  startPos <- getSourcePos
  try (void importKwP)
  (mn, _) <- moduleNameP
  endPos <- semi
  return (ImportDecl (Loc startPos endPos) mn)

setDeclP :: Parser Declaration
setDeclP = do
  startPos <- getSourcePos
  try (void setKwP)
  (txt,_) <- optionP
  endPos <- semi
  return (SetDecl (Loc startPos endPos) txt)

---------------------------------------------------------------------------------
-- Parsing Fixity Declarations
---------------------------------------------------------------------------------

assocP :: Parser (Assoc, SourcePos)
assocP = (infixlKwP >>= \sp -> pure (LeftAssoc, sp)) <|>
         (infixrKwP >>= \sp -> pure (RightAssoc, sp))

precedenceP :: Parser Precedence
precedenceP = do
  (p,_) <- numP
  pure $ MkPrecedence p

fixityDeclP :: Parser Declaration
fixityDeclP = do
  startPos <- getSourcePos
  (assoc, _) <- assocP
  prec <- precedenceP
  endPos <- semi
  pure $ FixityDecl (Loc startPos endPos) assoc prec

---------------------------------------------------------------------------------
-- Nominal type declaration parser
---------------------------------------------------------------------------------

xtorDeclP :: Parser (XtorName, [(PrdCns, Typ)])
xtorDeclP = do
  (xt, _pos) <- xtorName Nominal
  (args,_) <- argListsP typP
  return (xt, args )


argListToLctxt :: [(PrdCns, Typ)] -> LinearContext
argListToLctxt = fmap convert
  where
    convert (Prd, ty) = PrdType ty
    convert (Cns, ty) = CnsType ty

combineXtor :: (XtorName, [(PrdCns, Typ)]) -> XtorSig
combineXtor (xt, args) = MkXtorSig xt (argListToLctxt args)

combineXtors :: [(XtorName, [(PrdCns, Typ)])] -> [XtorSig]
combineXtors = fmap combineXtor

dataDeclP :: Parser Declaration
dataDeclP = do
  startPos <- getSourcePos
  dataCodata <- (dataKwP >> return Data) <|> (codataKwP >> return Codata)
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
    pure (DataDecl (Loc startPos endPos) decl)

---------------------------------------------------------------------------------
-- Parsing a program
---------------------------------------------------------------------------------

declarationP :: Parser Declaration
declarationP =
  prdCnsDeclarationP Prd <|>
  prdCnsDeclarationP Cns <|>
  cmdDeclarationP <|>
  importDeclP <|>
  setDeclP <|>
  fixityDeclP <|>
  dataDeclP

programP :: Parser Program
programP = do
  sc
  decls <- many declarationP
  eof
  return decls
