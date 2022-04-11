module Parser.Program
  ( declarationP
  , programP
  ) where

import Control.Monad (void)
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char (eol)

import Parser.Common
import Parser.Definition
import Parser.Lexer
import Parser.Terms
import Parser.Types
import Syntax.CST.Program
import Syntax.CST.Types
import Syntax.Common
import Utils

recoverDeclaration :: Parser Declaration -> Parser Declaration
recoverDeclaration = withRecovery (\err -> registerParseError err >> parseUntilKeywP >> return ParseErrorDecl)


---------------------------------------------------------------------------------
-- Producer/Consumer/Command Declarations
---------------------------------------------------------------------------------

isRecP :: Parser IsRec
isRecP = option NonRecursive (try (keywordP KwRec) >> pure Recursive)

annotP :: Parser (Maybe TypeScheme)
annotP = optional (try (notFollowedBy (symbolP SymColoneq) *> symbolP SymColon) >> typeSchemeP)

prdCnsDeclarationP :: Maybe DocComment -> SourcePos -> PrdCns -> Parser Declaration
prdCnsDeclarationP doc startPos pc = do
    (isRec, v) <- try $ do
      isRec <- isRecP
      (v, _pos) <- freeVarNameP
      _ <- (case pc of Prd -> brackets (symbolP SymImplicit); Cns -> parens (symbolP SymImplicit))
      pure (isRec, v)
    annot <- annotP
    _ <- symbolP SymColoneq
    (tm,_) <- termP
    endPos <- symbolP SymSemi
    pure (PrdCnsDecl (Loc startPos endPos) doc pc isRec v annot tm)

cmdDeclarationP :: Maybe DocComment -> SourcePos -> Parser Declaration
cmdDeclarationP doc startPos = do
    v <- try $ do
      (v, _pos) <- freeVarNameP
      _ <- symbolP SymColoneq
      pure v
    (cmd,_) <- commandP
    endPos <- symbolP SymSemi
    pure (CmdDecl (Loc startPos endPos) doc v cmd)

defDeclarationP :: Maybe DocComment -> Parser Declaration
defDeclarationP doc = do
  startPos <- getSourcePos
  try (void (keywordP KwDef))
  recoverDeclaration $ cmdDeclarationP doc startPos <|> prdCnsDeclarationP doc startPos Prd <|> prdCnsDeclarationP doc startPos Cns

---------------------------------------------------------------------------------
-- Import Declaration
---------------------------------------------------------------------------------

importDeclP :: Maybe DocComment -> Parser Declaration
importDeclP doc = do
  startPos <- getSourcePos
  try (void (keywordP KwImport))
  (mn, _) <- moduleNameP
  endPos <- symbolP SymSemi
  return (ImportDecl (Loc startPos endPos) doc mn)

---------------------------------------------------------------------------------
-- Set Option Declaration
---------------------------------------------------------------------------------

setDeclP :: Maybe DocComment -> Parser Declaration
setDeclP doc = do
  startPos <- getSourcePos
  try (void (keywordP KwSet))
  (txt,_) <- allCaseId
  endPos <- symbolP SymSemi
  return (SetDecl (Loc startPos endPos) doc txt)

---------------------------------------------------------------------------------
-- Type Operator Declaration
---------------------------------------------------------------------------------


-- | Parses a type operator declaration of the form
--       "type operator -> at 5 := Fun;"
typeOperatorDeclP :: Maybe DocComment -> Parser Declaration
typeOperatorDeclP doc = do
  startPos <- getSourcePos
  try (void (keywordP KwType *> keywordP KwOperator))
  recoverDeclaration $ do
    (sym,_) <- tyOpNameP
    assoc <- associativityP
    _ <- keywordP KwAt
    prec <- precedenceP
    _ <- symbolP SymColoneq
    (tyname,_) <- typeNameP
    endPos <- symbolP SymSemi
    pure (TyOpDecl (Loc startPos endPos) doc sym prec assoc tyname)

---------------------------------------------------------------------------------
-- Type Synonym parser
---------------------------------------------------------------------------------

tySynP :: Maybe DocComment -> Parser Declaration
tySynP doc = do
  startPos <- getSourcePos
  _ <- keywordP KwType
  recoverDeclaration $ do
    (tn,_) <- typeNameP
    _ <- symbolP SymColoneq
    (ty, _) <- typP
    endPos <- symbolP SymSemi
    pure (TySynDecl (Loc startPos endPos) doc tn ty)

---------------------------------------------------------------------------------
-- Nominal type declaration parser
---------------------------------------------------------------------------------

xtorDeclP :: Parser (XtorName, [(PrdCns, Typ)])
xtorDeclP = do
  (xt, _pos) <- xtorNameP <?> "constructor/destructor name"
  (args,_) <- argListsP False (fst <$> typP) <?> "argument list"
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

dataCodataPrefixP :: Parser (IsRefined,DataCodata)
dataCodataPrefixP = do
  refined <- optional (keywordP KwRefinement)
  dataCodata <- (keywordP KwData >> return Data) <|> (keywordP KwCodata >> return Codata)
  case refined of
    Nothing -> pure (NotRefined, dataCodata)
    Just _ -> pure (Refined, dataCodata)

dataDeclP :: Maybe DocComment -> Parser Declaration
dataDeclP doc = do
  o <- getOffset
  startPos <- getSourcePos
  (refined, dataCodata) <- dataCodataPrefixP
  recoverDeclaration $ do
    (tn, _pos) <- typeNameP
    knd <- optional (try (symbolP SymColon) >> polyKindP)
    knd' <- case knd of
      Nothing -> pure Nothing
      Just knd -> do
        if refined == Refined && not (null (allTypeVars knd))
          then region (setErrorOffset o) (fail "Parametrized refinement types are not supported, yet")
          else pure (Just knd)
    (xtors, _pos) <- braces $ xtorDeclP `sepBy` symbolP SymComma
    endPos <- symbolP SymSemi
    let decl = NominalDecl
              { data_refined = refined
              , data_name = tn
              , data_polarity = dataCodata
              , data_kind = knd'
              , data_xtors = combineXtors xtors
              }
    pure (DataDecl (Loc startPos endPos) doc decl)

---------------------------------------------------------------------------------
-- Xtor Declaration Parser
---------------------------------------------------------------------------------

-- | Parses either "constructor" or "destructor"
ctorDtorP :: Parser DataCodata
ctorDtorP = (keywordP KwConstructor >> pure Data) <|> (keywordP KwDestructor >> pure Codata)

xtorDeclarationP :: Maybe DocComment -> Parser Declaration
xtorDeclarationP doc = do
  startPos <- getSourcePos
  dc <- ctorDtorP
  (xt, _) <- xtorNameP
  (args, _) <- argListsP False monoKindP
  ret <- optional (try (symbolP SymColon) >> evalOrderP)
  endPos <- symbolP SymSemi
  pure (XtorDecl (Loc startPos endPos) doc dc xt args ret)

---------------------------------------------------------------------------------
-- Parsing a program
---------------------------------------------------------------------------------

docDeclarationP :: Maybe DocComment -> Parser Declaration
docDeclarationP doc =
  typeOperatorDeclP doc <|>
  defDeclarationP doc <|>
  importDeclP doc <|>
  setDeclP doc <|>
  dataDeclP doc <|>
  xtorDeclarationP doc <|>
  tySynP doc

declarationP :: Parser Declaration
declarationP = do
  doc <- optional ((fst <$> docCommentP) <* eol)
  docDeclarationP doc


programP :: Parser Program
programP = do
  sc
  decls <- many declarationP
  eof
  return decls
