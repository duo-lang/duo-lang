module Parser.Program
  ( declarationP
  , moduleP
  , moduleNameP
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
import Syntax.CST.Kinds (EvaluationOrder(..),PolyKind(..))
import Loc


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
    tm <- termP
    symbolP SymSemi
    endPos <- getSourcePos
    sc
    let decl = MkPrdCnsDeclaration { loc = Loc startPos endPos
                                   , doc = doc
                                   , prd_cns = pc
                                   , isRecursive = isRec
                                   , name = v
                                   , annot = annot
                                   , term = tm
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
    cmd <- termP
    symbolP SymSemi
    endPos <- getSourcePos
    sc
    let decl = MkCommandDeclaration { loc = Loc startPos endPos
                                    , doc = doc
                                    , name = v
                                    , cmd = cmd
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
  let decl = MkImportDeclaration { loc = Loc startPos endPos
                                 , doc = doc
                                 , mod = mn
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
  let decl = MkSetDeclaration { loc = Loc startPos endPos
                              , doc = doc
                              , option = txt
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
    let decl = MkTyOpDeclaration { loc = Loc startPos endPos
                                 , doc = doc
                                 , symbol = sym
                                 , precedence = prec
                                 , associativity = assoc
                                 , res = tyname
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
    let decl = MkTySynDeclaration { loc = Loc startPos endPos
                                  , doc = doc
                                  , name = tn
                                  , res = ty
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
    pure $ DataDecl $ MkDataDecl { loc = Loc startPos endPos
                                 , doc = doc
                                 , isRefined = refined
                                 , name = tn
                                 , data_codata = dataCodata
                                 , kind = knd
                                 , xtors = combineXtors xtors
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
  let decl = MkStructuralXtorDeclaration { loc = Loc startPos endPos
                                         , doc = doc
                                         , data_codata = dc
                                         , name = xt
                                         , arity = Data.Maybe.fromMaybe [] args
                                         , evalOrder = ret
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
    let decl = MkClassDeclaration (Loc startPos endPos) doc className (MkPolyKind typeVars CBV) xtors
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
    instanceName <- fst <$> (freeVarNameP <* sc)
    symbolP SymColon <* sc
    className    <- fst <$> (classNameP <* sc)
    typ          <- fst <$> typP
    (cases, _)   <- bracesP (termCaseP `sepBy` (symbolP SymComma >> sc))
    sc
    symbolP SymSemi
    endPos <- getSourcePos
    sc
    let decl = MkInstanceDeclaration (Loc startPos endPos) doc instanceName className typ cases
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

moduleDeclP :: Parser ModuleName
moduleDeclP = do
    --  startPos <- getSourcePos
    void $ keywordP KwModule
    sc
    (mn, _endPos) <- moduleNameP
    sc
    symbolP SymSemi
    sc
    return mn

moduleP :: FilePath -> Parser Module
moduleP libp = do
  sc
  mn <- moduleDeclP
  decls <- many declarationP
  eof
  pure MkModule { name = mn
                , libpath = libp
                , decls = decls
                }
