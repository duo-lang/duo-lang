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
import Syntax.Lowering.Types
import Syntax.CommonTerm
import Syntax.AST.Types (PolarityRep, DataDecl(..), DataCodata(..))
import Syntax.AST.Types qualified as AST
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
-- Nominal type declaration parser
---------------------------------------------------------------------------------

---------------------------------------------------------------------------------
-- Parsing of invariant Types (HACKY!)
---------------------------------------------------------------------------------

newtype Invariant = MkInvariant { unInvariant :: forall pol. PolarityRep pol -> AST.Typ pol }

invariantP :: Parser Invariant
invariantP = do
  typ <- typAtomP
  pure $ MkInvariant $ \rep ->
    case lowerTyp rep typ of
      Right typ -> typ
      -- FIXME: Adjust AST such that it can handle lazy lowering/polarization properly
      Left err -> error (show err)

xtorDeclP :: Parser (XtorName, [(PrdCns, Invariant)])
xtorDeclP = do
  (xt, _pos) <- xtorName Nominal
  (args,_) <- argListsP invariantP
  return (xt, args )

combineXtors :: [(XtorName, [(PrdCns, Invariant)])] -> (forall pol. PolarityRep pol -> [AST.XtorSig pol])
combineXtors [] = \_rep -> []
combineXtors ((xt, args):rest) = \rep -> (AST.MkXtorSig xt (f rep <$> args)) : combineXtors rest rep
  where
    f rep (Prd, x) = AST.PrdCnsType PrdRep $ unInvariant x rep
    f rep (Cns, x) = AST.PrdCnsType CnsRep $ unInvariant x (AST.flipPolarityRep rep)


dataDeclP :: Parser Declaration
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

declarationP :: Parser Declaration
declarationP =
  prdCnsDeclarationP Prd <|>
  prdCnsDeclarationP Cns <|>
  cmdDeclarationP <|>
  importDeclP <|>
  setDeclP <|>
  dataDeclP

programP :: Parser Program
programP = do
  sc
  decls <- many declarationP
  eof
  return decls
