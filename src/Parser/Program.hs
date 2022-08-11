module Parser.Program
  ( declarationP
  , programP
  , returnP
  , xtorDeclP
  , xtorSignatureP
  ) where

import Control.Monad (void)
import Data.Maybe qualified
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char (eol)

import Parser.Common
import Parser.Definition
import Parser.Lexer
import Parser.Terms
import Parser.Types
import Syntax.CST.Program
import Syntax.CST.Types
import Syntax.Common.PrdCns
import Syntax.RST.Names
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
      _ <- (case pc of Prd -> keywordP KwPrd ; Cns -> keywordP KwCns)
      (v, _pos) <- freeVarNameP
      pure (isRec, v)
    annot <- annotP
    _ <- symbolP SymColoneq
    (tm,_) <- termP
    endPos <- symbolP SymSemi
    let decl = MkPrdCnsDeclaration { pcdecl_loc = Loc startPos endPos
                                   , pcdecl_doc = doc
                                   , pcdecl_pc = pc
                                   , pcdecl_isRec = isRec
                                   , pcdecl_name = v
                                   , pcdecl_annot = annot
                                   , pcdecl_term = tm
                                   }
    pure (PrdCnsDecl decl)

cmdDeclarationP :: Maybe DocComment -> SourcePos -> Parser Declaration
cmdDeclarationP doc startPos = do
    v <- try $ do
      _ <- keywordP KwCmd
      (v, _pos) <- freeVarNameP
      _ <- symbolP SymColoneq
      pure v
    (cmd,_) <- termP
    endPos <- symbolP SymSemi
    let decl = MkCommandDeclaration { cmddecl_loc = Loc startPos endPos
                                    , cmddecl_doc = doc
                                    , cmddecl_name = v
                                    , cmddecl_cmd = cmd
                                    }
    pure (CmdDecl decl)

defDeclarationP :: Maybe DocComment -> Parser Declaration
defDeclarationP doc = do
  startPos <- getSourcePos
  try (void (keywordP KwDef))
  recoverDeclaration $
    cmdDeclarationP doc startPos <|>
    prdCnsDeclarationP doc startPos Prd <|>
    prdCnsDeclarationP doc startPos Cns

---------------------------------------------------------------------------------
-- Import Declaration
---------------------------------------------------------------------------------

importDeclP :: Maybe DocComment -> Parser Declaration
importDeclP doc = do
  startPos <- getSourcePos
  try (void (keywordP KwImport))
  (mn, _) <- moduleNameP
  endPos <- symbolP SymSemi
  let decl = MkImportDeclaration { imprtdecl_loc = Loc startPos endPos
                                 , imprtdecl_doc = doc
                                 , imprtdecl_module = mn
                                 }
  return (ImportDecl decl)

---------------------------------------------------------------------------------
-- Set Option Declaration
---------------------------------------------------------------------------------

setDeclP :: Maybe DocComment -> Parser Declaration
setDeclP doc = do
  startPos <- getSourcePos
  try (void (keywordP KwSet))
  (txt,_) <- allCaseId
  endPos <- symbolP SymSemi
  let decl = MkSetDeclaration { setdecl_loc = Loc startPos endPos
                              , setdecl_doc = doc
                              , setdecl_option = txt
                              }
  return (SetDecl decl)

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
    let decl = MkTyOpDeclaration { tyopdecl_loc = Loc startPos endPos
                                 , tyopdecl_doc = doc
                                 , tyopdecl_sym = sym
                                 , tyopdecl_prec = prec
                                 , tyopdecl_assoc = assoc
                                 , tyopdecl_res = tyname
                                 }
    pure (TyOpDecl decl)

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
    let decl = MkTySynDeclaration { tysyndecl_loc = Loc startPos endPos
                                  , tysyndecl_doc = doc
                                  , tysyndecl_name = tn
                                  , tysyndecl_res = ty
                                  }
    pure (TySynDecl decl)

---------------------------------------------------------------------------------
-- Nominal type declaration parser
---------------------------------------------------------------------------------

dataCodataPrefixP :: Parser (IsRefined,DataCodata)
dataCodataPrefixP = do
  refined <- optional (keywordP KwRefinement)
  dataCodata <- (keywordP KwData >> return Data) <|> (keywordP KwCodata >> return Codata)
  case refined of
    Nothing -> pure (NotRefined, dataCodata)
    Just _ -> pure (Refined, dataCodata)

dataDeclP :: Maybe DocComment -> Parser Declaration
dataDeclP doc = do
  startPos <- getSourcePos
  (refined, dataCodata) <- dataCodataPrefixP
  recoverDeclaration $ do
    (tn, _pos) <- typeNameP
    knd <- optional (try (symbolP SymColon) >> polyKindP)
    (xtors, _pos) <- braces (xtorDeclP `sepBy` symbolP SymComma)
    endPos <- symbolP SymSemi
    pure $ DataDecl $ MkDataDecl { data_loc = Loc startPos endPos
                                  , data_doc = doc
                                  , data_refined = refined
                                  , data_name = tn
                                  , data_polarity = dataCodata
                                  , data_kind = knd
                                  , data_xtors = combineXtors xtors
                                  }

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
  args <- optional $ fst <$> (parens (returnP monoKindP `sepBy` symbolP SymComma) <?> "argument list") --argListsP False monoKindP
  ret <- optional (try (symbolP SymColon) >> evalOrderP)
  endPos <- symbolP SymSemi
  let decl = MkStructuralXtorDeclaration { strxtordecl_loc = Loc startPos endPos
                                         , strxtordecl_doc = doc
                                         , strxtordecl_xdata = dc
                                         , strxtordecl_name = xt
                                         , strxtordecl_arity = Data.Maybe.fromMaybe [] args
                                         , strxtordecl_evalOrder = ret
                                         }
  pure (XtorDecl decl)

---------------------------------------------------------------------------------
-- Parsing a class declaration
---------------------------------------------------------------------------------

classDeclarationP :: Maybe DocComment -> Parser Declaration
classDeclarationP doc = do
  startPos <- getSourcePos
  try (void (keywordP KwClass))
  recoverDeclaration $ do
    className     <- fst <$> classNameP
    typeVars      <- fst <$> parens (tParamP `sepBy` symbolP SymComma)
    (xtors, _pos) <- braces (xtorSignatureP `sepBy` symbolP SymComma)
    endPos        <- symbolP SymSemi
    let decl = MkClassDeclaration (Loc startPos endPos) doc className typeVars xtors
    pure (ClassDecl decl)


---------------------------------------------------------------------------------
-- Parsing an instance declaration
---------------------------------------------------------------------------------

instanceDeclarationP :: Maybe DocComment -> Parser Declaration
instanceDeclarationP doc = do
  startPos <- getSourcePos
  try (void (keywordP KwInstance))
  recoverDeclaration $ do
    className  <- fst <$> classNameP
    typ        <- fst <$> typP
    (cases, _) <- braces ((fst <$> termCaseP) `sepBy` symbolP SymComma)
    endPos     <- symbolP SymSemi
    let decl = MkInstanceDeclaration (Loc startPos endPos) doc className typ cases
    pure (InstanceDecl decl)


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
  tySynP doc <|>
  classDeclarationP doc <|>
  instanceDeclarationP doc

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
