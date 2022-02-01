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
import Syntax.CST.LoweringTerms
import Syntax.CST.LoweringTypes
import Syntax.Program
import Syntax.Types
import Syntax.Types qualified as AST
import Syntax.CommonTerm
import Utils (Loc(..))

recoverDeclaration :: Parser (Declaration Parsed) -> Parser (Declaration Parsed)
recoverDeclaration = withRecovery (\err -> registerParseError err >> parseUntilKeywP >> return ParseErrorDecl)

isRecP :: Parser IsRec
isRecP = option NonRecursive (try recKwP >> pure Recursive)

annotP :: PolarityRep pol -> Parser (Maybe (TypeScheme pol))
annotP rep = do
  maybeAnnot <- optional (try (notFollowedBy coloneq *> colon) >> typeSchemeP)
  case maybeAnnot of
    Nothing -> pure Nothing
    Just annot -> case lowerTypeScheme rep annot of
      Left err -> fail (show err)
      Right res -> pure (Just res)
  

prdCnsDeclarationP :: PrdCnsRep pc -> Parser (Declaration Parsed)
prdCnsDeclarationP PrdRep = do
  startPos <- getSourcePos
  try (void prdKwP)
  recoverDeclaration $ do
    isRec <- isRecP
    (v, _pos) <- freeVarName
    annot <- annotP PosRep
    _ <- coloneq
    (tm,_) <- termP
    endPos <- semi
    case lowerTerm PrdRep tm of
      Left err -> fail (show err)
      Right res -> return (PrdCnsDecl (Loc startPos endPos) PrdRep isRec v annot res)
prdCnsDeclarationP CnsRep = do
  startPos <- getSourcePos
  try (void cnsKwP)
  recoverDeclaration $ do
    isRec <- isRecP
    (v, _pos) <- freeVarName
    annot <- annotP NegRep
    _ <- coloneq
    (tm,_) <- termP
    endPos <- semi
    case lowerTerm CnsRep tm of
      Left err -> fail (show err)
      Right res -> return (PrdCnsDecl (Loc startPos endPos) CnsRep isRec v annot res)

cmdDeclarationP :: Parser (Declaration Parsed)
cmdDeclarationP = do
  startPos <- getSourcePos
  try (void cmdKwP)
  recoverDeclaration $ do
    (v, _pos) <- freeVarName
    _ <- coloneq
    (cmd,_) <- commandP
    endPos <- semi
    case lowerCommand cmd of
      Left err -> fail (show err)
      Right res -> return (CmdDecl (Loc startPos endPos) v res)

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

combineXtors :: [(XtorName, [(PrdCns, Invariant)])] -> (forall pol. PolarityRep pol -> [XtorSig pol])
combineXtors [] = \_rep -> []
combineXtors ((xt, args):rest) = \rep -> (MkXtorSig xt (f rep <$> args)) : combineXtors rest rep
  where
    f rep (Prd, x) = PrdCnsType PrdRep $ unInvariant x rep
    f rep (Cns, x) = PrdCnsType CnsRep $ unInvariant x (flipPolarityRep rep)


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
