module Parser.Program
  ( declarationP
  , programP
  ) where

import Control.Monad (void)
import Control.Monad.Reader ( MonadReader(local) )
import Text.Megaparsec hiding (State)

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

isRecP :: Parser IsRec
isRecP = option NonRecursive (try (keywordP KwRec) >> pure Recursive)

annotP :: Parser (Maybe TypeScheme)
annotP = optional (try (notFollowedBy (symbolP SymColoneq) *> symbolP SymColon) >> typeSchemeP)

prdCnsDeclarationP :: SourcePos -> PrdCns -> Parser Declaration
prdCnsDeclarationP startPos pc = do
    (isRec, v) <- try $ do
      isRec <- isRecP
      (v, _pos) <- freeVarName
      _ <- (case pc of Prd -> brackets (symbolP SymImplicit); Cns -> parens (symbolP SymImplicit))
      pure (isRec, v)
    annot <- annotP
    _ <- symbolP SymColoneq
    (tm,_) <- termP
    endPos <- symbolP SymSemi
    pure (PrdCnsDecl (Loc startPos endPos) pc isRec v annot tm)

cmdDeclarationP :: SourcePos -> Parser Declaration
cmdDeclarationP startPos = do
    v <- try $ do
      (v, _pos) <- freeVarName
      _ <- symbolP SymColoneq
      pure v
    (cmd,_) <- commandP
    endPos <- symbolP SymSemi
    pure (CmdDecl (Loc startPos endPos) v cmd)

defDeclarationP :: Parser Declaration
defDeclarationP = do
  startPos <- getSourcePos
  try (void (keywordP KwDef))
  recoverDeclaration $ cmdDeclarationP startPos <|> prdCnsDeclarationP startPos Prd <|> prdCnsDeclarationP startPos Cns

---------------------------------------------------------------------------------
-- Import Declaration
---------------------------------------------------------------------------------

importDeclP :: Parser Declaration
importDeclP = do
  startPos <- getSourcePos
  try (void (keywordP KwImport))
  (mn, _) <- moduleNameP
  endPos <- symbolP SymSemi
  return (ImportDecl (Loc startPos endPos) mn)

---------------------------------------------------------------------------------
-- Set Option Declaration
---------------------------------------------------------------------------------

setDeclP :: Parser Declaration
setDeclP = do
  startPos <- getSourcePos
  try (void (keywordP KwSet))
  (txt,_) <- allCaseId
  endPos <- symbolP SymSemi
  return (SetDecl (Loc startPos endPos) txt)

---------------------------------------------------------------------------------
-- Type Operator Declaration
---------------------------------------------------------------------------------

precedenceP :: Parser Precedence
precedenceP = do
  (n,_) <- natP
  pure (MkPrecedence n)

-- | Parses a type operator declaration of the form
--       "type operator -> at 5 := Fun;"
typeOperatorDeclP :: Parser Declaration
typeOperatorDeclP = do
  startPos <- getSourcePos
  try (void (keywordP KwType))
  _ <- keywordP KwOperator
  (sym,_) <- tyOpNameP
  _ <- keywordP KwAt
  prec <- precedenceP
  _ <- symbolP SymColoneq
  (tyname,_) <- typeNameP
  endPos <- symbolP SymSemi
  pure (TyOpDecl (Loc startPos endPos) sym prec tyname)

---------------------------------------------------------------------------------
-- Nominal type declaration parser
---------------------------------------------------------------------------------

xtorDeclP :: Parser (XtorName, [(PrdCns, Typ)])
xtorDeclP = do
  (xt, _pos) <- xtorName
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

dataCodataPrefixP :: Parser (IsRefined,DataCodata)
dataCodataPrefixP = do
  refined <- optional (keywordP KwRefinement)
  dataCodata <- (keywordP KwData >> return Data) <|> (keywordP KwCodata >> return Codata)
  case refined of
    Nothing -> pure (NotRefined, dataCodata)
    Just _ -> pure (Refined, dataCodata)

dataDeclP :: Parser Declaration
dataDeclP = do
  o <- getOffset
  startPos <- getSourcePos
  (refined, dataCodata) <- dataCodataPrefixP
  recoverDeclaration $ do
    (tn, _pos) <- typeNameP
    knd <- optional (try (symbolP SymColon) >> polyKindP)
    case knd of
      Nothing -> do
        (xtors, _pos) <- braces $ xtorDeclP `sepBy` symbolP SymComma
        endPos <- symbolP SymSemi
        let decl = NominalDecl
              { data_refined = refined
              , data_name = tn
              , data_polarity = dataCodata
              , data_kind = knd
              , data_xtors = combineXtors xtors
              }
        pure (DataDecl (Loc startPos endPos) decl)
      Just knd -> do
        if refined == Refined && not (null (allTypeVars knd)) then
          region (setErrorOffset o) (fail "Parametrized refinement types are not supported, yet")
        else
          do
            let xtorP = local (\s -> s { tvars = allTypeVars knd }) xtorDeclP
            (xtors, _pos) <- braces $ xtorP `sepBy` symbolP SymComma
            endPos <- symbolP SymSemi
            let decl = NominalDecl
                  { data_refined = refined
                  , data_name = tn
                  , data_polarity = dataCodata
                  , data_kind = Just knd
                  , data_xtors = combineXtors xtors
                  }
            pure (DataDecl (Loc startPos endPos) decl)

---------------------------------------------------------------------------------
-- Xtor Declaration Parser
---------------------------------------------------------------------------------

-- | Parses either "constructor" or "destructor"
ctorDtorP :: Parser DataCodata
ctorDtorP = (keywordP KwConstructor >> pure Data) <|> (keywordP KwDestructor >> pure Codata)

xtorDeclarationP :: Parser Declaration
xtorDeclarationP = do
  startPos <- getSourcePos
  dc <- ctorDtorP
  (xt, _) <- xtorName
  (args, _) <- argListsP monoKindP
  ret <- optional (try (symbolP SymColon) >> evalOrderP)
  endPos <- symbolP SymSemi
  pure (XtorDecl (Loc startPos endPos) dc xt args ret)

---------------------------------------------------------------------------------
-- Parsing a program
---------------------------------------------------------------------------------

declarationP :: Parser Declaration
declarationP =
  typeOperatorDeclP <|>
  defDeclarationP <|>
  importDeclP <|>
  setDeclP <|>
  dataDeclP <|>
  xtorDeclarationP

programP :: Parser Program
programP = do
  sc
  decls <- many declarationP
  eof
  return decls
