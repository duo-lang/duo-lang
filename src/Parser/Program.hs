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
  refined <- optional refinementKwP
  dataCodata <- (dataKwP >> return Data) <|> (codataKwP >> return Codata)
  case refined of
    Nothing -> pure (NotRefined, dataCodata)
    Just _ -> pure (Refined, dataCodata)

varianceP :: Variance -> Parser ()
varianceP Covariant = void plusSym
varianceP Contravariant = void minusSym

polyKindP :: Parser PolyKind
polyKindP = do
  (contra, cov) <- tparamsP
  _ <- colon
  ret <- evalOrderP
  pure (MkPolyKind contra cov ret)

tParamP :: Variance -> Parser (TVar, Kind)
tParamP v = do
  _ <- varianceP v
  (tvar,_) <- tvarP
  _ <- colon
  kind <- kindP
  pure (tvar, kind)

tparamsP :: Parser ([(TVar, Kind)],[(TVar, Kind)])
tparamsP =
  (fst <$> parens inner) <|> pure ([],[])
  where
    inner = do
      con_ps <- tParamP Contravariant `sepBy` try (comma <* notFollowedBy (varianceP Covariant))
      if null con_ps then
        (\x -> ([], x)) <$> tParamP Covariant `sepBy` comma
      else do
        cov_ps <-
          try comma *> tParamP Covariant `sepBy` comma
          <|> pure []
        pure (con_ps, cov_ps)

dataDeclP :: Parser Declaration
dataDeclP = do
  o <- getOffset
  startPos <- getSourcePos
  (refined, dataCodata) <- dataCodataPrefixP
  recoverDeclaration $ do
    (tn, _pos) <- typeNameP
    knd <- polyKindP
    if refined == Refined && not (null (allTypeVars knd)) then
      region (setErrorOffset o) (fail "Parametrized refinement types are not supported, yet")
    else
      do
        let xtorP = local (\s -> s { tvars = allTypeVars knd }) xtorDeclP
        (xtors, _pos) <- braces $ xtorP `sepBy` comma
        endPos <- semi
        let decl = NominalDecl
              { data_refined = refined
              , data_name = tn
              , data_polarity = dataCodata
              , data_kind = knd
              , data_xtors = combineXtors xtors
              }

        pure (DataDecl (Loc startPos endPos) decl)

---------------------------------------------------------------------------------
-- Xtor Declaration Parser
---------------------------------------------------------------------------------

-- | Parses either "constructor" or "destructor"
ctorDtorP :: Parser DataCodata
ctorDtorP = (constructorKwP >> pure Data) <|> (destructorKwP >> pure Codata)

xtorDeclarationP :: Parser Declaration
xtorDeclarationP = do
  startPos <- getSourcePos
  dc <- ctorDtorP
  (xt, _) <- xtorName
  (args, _) <- argListsP callingConventionP
  _ <- colon
  ret <- callingConventionP
  endPos <- semi
  pure (XtorDecl (Loc startPos endPos) dc xt args ret)

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
  dataDeclP <|>
  xtorDeclarationP

programP :: Parser Program
programP = do
  sc
  decls <- many declarationP
  eof
  return decls
