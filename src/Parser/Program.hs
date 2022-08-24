module Parser.Program
  ( declarationP
  , moduleP
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
import Parser.Kinds
import Parser.Lexer
import Parser.Terms
import Parser.Types
import Syntax.CST.Program
import Syntax.CST.Types
import Syntax.CST.Names
import Utils

recoverDeclaration :: Parser Declaration -> Parser Declaration
recoverDeclaration = withRecovery (\err -> registerParseError err >> parseUntilKeywP >> return ParseErrorDecl)


---------------------------------------------------------------------------------
-- Producer/Consumer/Command Declarations
---------------------------------------------------------------------------------

isRecP :: Parser IsRec
isRecP = option NonRecursive (try (keywordP KwRec >> sc) >> pure Recursive)

annotP :: Parser (Maybe TypeScheme)
annotP = optional (try (notFollowedBy (symbolP SymColoneq >> sc) *> (symbolP SymColon >> sc)) >> typeSchemeP)

prdCnsDeclarationP :: Maybe DocComment -> SourcePos -> PrdCns -> Parser Declaration
prdCnsDeclarationP doc startPos pc = do
    (isRec, v) <- try $ do
      isRec <- isRecP
      _ <- (case pc of Prd -> keywordP KwPrd ; Cns -> keywordP KwCns)
      sc
      (v, _pos) <- freeVarNameP
      sc
      pure (isRec, v)
    annot <- annotP
    symbolP SymColoneq
    sc
    (tm,_) <- termP
    symbolP SymSemi
    endPos <- getSourcePos
    sc
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
      sc
      (v, _pos) <- freeVarNameP
      sc
      symbolP SymColoneq
      sc
      pure v
    (cmd,_) <- termP
    symbolP SymSemi
    endPos <- getSourcePos
    sc
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
  sc
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
  sc
  (mn, _) <- moduleNameP
  sc
  symbolP SymSemi
  endPos <- getSourcePos
  sc
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
  sc
  (txt,_) <- allCaseIdL
  sc
  symbolP SymSemi
  endPos <- getSourcePos
  sc
  let decl = MkSetDeclaration { setdecl_loc = Loc startPos endPos
                              , setdecl_doc = doc
                              , setdecl_option = txt
                              }
  return (SetDecl decl)

---------------------------------------------------------------------------------
-- Type Operator Declaration
---------------------------------------------------------------------------------

precedenceP :: Parser Precedence
precedenceP = do
  (n,_) <- natP
  sc
  pure (MkPrecedence n)

associativityP :: Parser Associativity
associativityP = leftAssoc <|> rightAssoc
  where
    leftAssoc  = keywordP KwLeftAssoc  >> sc >> pure LeftAssoc
    rightAssoc = keywordP KwRightAssoc >> sc >> pure RightAssoc

-- | Parses a type operator declaration of the form
--       "type operator -> at 5 := Fun;"
typeOperatorDeclP :: Maybe DocComment -> Parser Declaration
typeOperatorDeclP doc = do
  startPos <- getSourcePos
  try (void (keywordP KwType >> sc >> keywordP KwOperator))
  sc
  recoverDeclaration $ do
    (sym,_) <- tyOpNameP
    sc
    assoc <- associativityP
    _ <- keywordP KwAt
    sc
    prec <- precedenceP
    symbolP SymColoneq
    sc
    (tyname,_) <- typeNameP
    sc
    symbolP SymSemi
    endPos <- getSourcePos
    sc
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
  sc
  recoverDeclaration $ do
    (tn,_) <- typeNameP
    sc
    symbolP SymColoneq
    sc
    (ty, _) <- typP
    symbolP SymSemi
    endPos <- getSourcePos
    sc
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
  refined <- optional (keywordP KwRefinement >> sc)
  dataCodata <- (keywordP KwData >> return Data) <|> (keywordP KwCodata >> return Codata)
  sc
  case refined of
    Nothing -> pure (NotRefined, dataCodata)
    Just _ -> pure (Refined, dataCodata)

dataDeclP :: Maybe DocComment -> Parser Declaration
dataDeclP doc = do
  startPos <- getSourcePos
  (refined, dataCodata) <- dataCodataPrefixP
  recoverDeclaration $ do
    (tn, _pos) <- typeNameP
    sc
    knd <- optional (try (symbolP SymColon >> sc) >> polyKindP)
    (xtors, _pos) <- bracesP (xtorDeclP `sepBy` (symbolP SymComma >> sc))
    sc
    symbolP SymSemi
    endPos <- getSourcePos
    sc
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
ctorDtorP = (keywordP KwConstructor >> sc >> pure Data) <|> (keywordP KwDestructor >> sc >> pure Codata)

xtorDeclarationP :: Maybe DocComment -> Parser Declaration
xtorDeclarationP doc = do
  startPos <- getSourcePos
  dc <- ctorDtorP
  (xt, _) <- xtorNameP
  sc
  args <- optional $ do 
    (args,_) <- parensP (returnP monoKindP `sepBy` (symbolP SymComma >> sc)) <?> "argument list"
    sc
    pure args
  ret <- optional (try (symbolP SymColon >> sc) >> evalOrderP)
  symbolP SymSemi
  endPos <- getSourcePos
  sc
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
  sc
  recoverDeclaration $ do
    className     <- fst <$> (classNameP <* sc)
    typeVars      <- fst <$> parensP (tParamP `sepBy` (symbolP SymComma >> sc))
    sc
    (xtors, _pos) <- bracesP (xtorSignatureP `sepBy` (symbolP SymComma >> sc))
    sc
    symbolP SymSemi
    endPos <- getSourcePos
    sc
    let decl = MkClassDeclaration (Loc startPos endPos) doc className typeVars xtors
    pure (ClassDecl decl)


---------------------------------------------------------------------------------
-- Parsing an instance declaration
---------------------------------------------------------------------------------

instanceDeclarationP :: Maybe DocComment -> Parser Declaration
instanceDeclarationP doc = do
  startPos <- getSourcePos
  try (void (keywordP KwInstance))
  sc
  recoverDeclaration $ do
    className  <- fst <$> (classNameP <* sc)
    typ        <- fst <$> typP
    (cases, _) <- bracesP ((fst <$> termCaseP) `sepBy` (symbolP SymComma >> sc))
    sc
    symbolP SymSemi
    endPos <- getSourcePos
    sc
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


moduleP :: ModuleName -> FilePath -> Parser Module
moduleP mn fp = do
  sc
  decls <- many declarationP
  eof
  pure MkModule { mod_name = mn
                , mod_fp = fp
                , mod_decls = decls
                }
