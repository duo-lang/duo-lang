module Parser
  ( runEnvParser , termP, commandP, declarationP, environmentP, typeSchemeP, subtypingProblemP, bindingP, Parser)
  where

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Reader

import Data.Void

import Eval.Substitution
import Syntax.Terms
import Syntax.Types
import Syntax.TypeGraph
import Syntax.Program
import Utils

-- A parser that can read values from an environment
type Parser = ReaderT Syntax.Program.Environment (Parsec Void String)

runEnvParser :: Parser a -> Syntax.Program.Environment -> String -> Either Error a
runEnvParser p env input = case runParser (runReaderT (lexeme (p <* eof)) env) "<interactive>" input of
  Left err -> Left $ ParseError (errorBundlePretty err)
  Right x -> Right x

-------------------------------------------------------------------------------------------
-- Generic Parsers
-------------------------------------------------------------------------------------------

sepBy2 :: MonadPlus m => m a -> m sep -> m [a]
sepBy2 p sep = (:) <$> (p <* sep) <*> (sepBy1 p sep)

sc :: (MonadParsec Void String m) => m ()
sc = L.space space1 (L.skipLineComment "#") (L.skipBlockComment "###" "###")

lexeme :: (MonadParsec Void String m) => m a -> m a
lexeme = L.lexeme sc

symbol :: (MonadParsec Void String m) => String -> m String
symbol = L.symbol sc

freeVarName :: (MonadParsec Void String m) => m FreeVarName
freeVarName = lexeme $ ((:) <$> lowerChar <*> many alphaNumChar) <|> symbol "_"

xtorName :: (MonadParsec Void String m) => NominalStructural -> m XtorName
xtorName Structural = do
  _ <- tick
  name <- (lexeme $ (:) <$> upperChar <*> many alphaNumChar)
  return (MkXtorName Structural name) -- Saved without tick!
xtorName Nominal = do
  name <- (lexeme $ (:) <$> upperChar <*> many alphaNumChar)
  return (MkXtorName Nominal name)

typeIdentifierName :: (MonadParsec Void String m) => m String
typeIdentifierName = lexeme $ (:) <$> upperChar <*> many alphaNumChar

parens, braces, brackets, angles :: (MonadParsec Void String m) => m a -> m a
parens    = between (symbol "(") (symbol ")")
braces    = between (symbol "{") (symbol "}")
brackets  = between (symbol "[") (symbol "]")
angles    = between (symbol "<") (symbol ">")

comma, dot, pipe, tick :: (MonadParsec Void String m) => m String
comma = symbol ","
dot = symbol "."
pipe = symbol "|"
tick = symbol "'"

-- | Parse two lists, the first in parentheses and the second in brackets.
argListP :: (MonadParsec Void String m) => m a -> m a ->  m (Twice [a])
argListP p q = do
  xs <- option [] (parens   $ p `sepBy` comma)
  ys <- option [] (brackets $ q `sepBy` comma)
  return $ Twice xs ys

--------------------------------------------------------------------------------------------
-- Term/Command parsing
--------------------------------------------------------------------------------------------

--nice helper function for creating xtor signatures
argsSig :: Int -> Int -> Twice [()]
argsSig n m = Twice (replicate n ()) (replicate m ())

-- nice helper function for creating natural numbers
numToTerm :: Int -> Term Prd ()
numToTerm 0 = XtorCall PrdRep (MkXtorName Structural "Z") (MkXtorArgs [] [])
numToTerm n = XtorCall PrdRep (MkXtorName Structural "S") (MkXtorArgs [numToTerm (n-1)] [])

termEnvP :: PrdCnsRep pc -> Parser (Term pc ())
termEnvP PrdRep = do
  v <- lexeme (many alphaNumChar)
  prdEnv <- asks prdEnv
  Just t <- return $  M.lookup v prdEnv
  return t
termEnvP CnsRep = do
  v <- lexeme (many alphaNumChar)
  cnsEnv <- asks cnsEnv
  Just t <- return $ M.lookup v cnsEnv
  return t

termP :: PrdCnsRep pc -> Parser (Term pc ())
termP pc = try (parens (termP pc))
  <|> xtorCall Structural pc
  <|> xtorCall Nominal pc
  -- We put the structural pattern match parser before the nominal one, since in the case of an empty match/comatch we want to
  -- infer a structural type, not a nominal one.
  <|> try (patternMatch Structural pc) 
  <|> try (patternMatch Nominal pc)
  <|> muAbstraction pc
  <|> try (termEnvP pc) -- needs to be tried, because the parser has to consume the string, before it checks
                        -- if the variable is in the environment, which might cause it to fail
  <|> freeVar pc
  <|> numLit pc
  <|> lambdaSugar pc

freeVar :: PrdCnsRep pc -> Parser (Term pc ())
freeVar pc = do
  v <- freeVarName
  return (FreeVar pc v ())

numLit :: PrdCnsRep pc -> Parser (Term pc ())
numLit CnsRep = empty
numLit PrdRep = numToTerm . read <$> some numberChar

lambdaSugar :: PrdCnsRep pc -> Parser (Term pc ())
lambdaSugar CnsRep = empty
lambdaSugar PrdRep= do
  _ <- lexeme (symbol "\\")
  args@(Twice prdVars cnsVars) <- argListP freeVarName freeVarName
  _ <- lexeme (symbol "=>")
  cmd <- lexeme commandP
  return $ Match PrdRep Structural [MkCase (MkXtorName Structural "Ap") (argsSig (length prdVars) (length cnsVars)) (commandClosing args cmd)]

-- | Parse two lists, the first in parentheses and the second in brackets.
xtorArgsP :: Parser (XtorArgs ())
xtorArgsP = do
  xs <- option [] (parens   $ (termP PrdRep) `sepBy` comma)
  ys <- option [] (brackets $ (termP CnsRep) `sepBy` comma)
  return $ MkXtorArgs xs ys

xtorCall :: NominalStructural -> PrdCnsRep pc -> Parser (Term pc ())
xtorCall ns pc = do
  xt <- xtorName ns
  args <- xtorArgsP
  return $ XtorCall pc xt args

patternMatch :: NominalStructural -> PrdCnsRep pc -> Parser (Term pc ())
patternMatch ns PrdRep = do
  _ <- symbol "comatch"
  cases <- braces $ singleCase ns `sepBy` comma
  return $ Match PrdRep ns cases
patternMatch ns CnsRep = do
  _ <- symbol "match"
  cases <- braces $ singleCase ns `sepBy` comma
  return $ Match CnsRep ns cases

singleCase :: NominalStructural -> Parser (Case ())
singleCase ns = do
  xt <- lexeme (xtorName ns)
  args@(Twice prdVars cnsVars) <- argListP freeVarName freeVarName
  _ <- symbol "=>"
  cmd <- lexeme commandP
  return MkCase { case_name = xt
                , case_args = argsSig (length prdVars) (length cnsVars)  -- e.g. X(x,y)[k] becomes X((),())[()]
                , case_cmd = commandClosing args cmd -- de brujin transformation
                }

muAbstraction :: PrdCnsRep pc -> Parser (Term pc ())
muAbstraction pc = do
  _ <- symbol (case pc of { PrdRep -> "mu"; CnsRep -> "mu*" })
  v <- lexeme freeVarName
  _ <- dot
  cmd <- lexeme commandP
  case pc of
    PrdRep -> return $ MuAbs pc () (commandClosingSingle CnsRep v cmd)
    CnsRep -> return $ MuAbs pc () (commandClosingSingle PrdRep v cmd)


commandP :: Parser (Command ())
commandP = try (parens commandP) <|> doneCmd <|> printCmd <|> applyCmd

applyCmd :: Parser (Command ())
applyCmd = do
  prd <- lexeme (termP PrdRep)
  _ <- lexeme (symbol ">>")
  cns <- lexeme (termP CnsRep)
  return (Apply prd cns)

doneCmd :: Parser (Command ())
doneCmd = lexeme (symbol "Done") >> return Done

printCmd :: Parser (Command ())
printCmd = lexeme (symbol "Print") >> (Print <$> lexeme (termP PrdRep))

---------------------------------------------------------------------------------
-- Parsing a program
---------------------------------------------------------------------------------

declarationP :: Parser (Declaration ())
declarationP = prdDeclarationP <|> cnsDeclarationP <|> typeDeclarationP <|> dataDeclP

prdDeclarationP :: Parser (Declaration ())
prdDeclarationP = do
  _ <- try $ lexeme (symbol "prd")
  v <- freeVarName
  _ <- lexeme (symbol ":=")
  t <- lexeme (termP PrdRep)
  _ <- symbol ";"
  return (PrdDecl v t)

cnsDeclarationP :: Parser (Declaration ())
cnsDeclarationP = do
  _ <- try $ lexeme (symbol "cns")
  v <- freeVarName
  _ <- lexeme (symbol ":=")
  t <- lexeme (termP CnsRep)
  _ <- symbol ";"
  return (CnsDecl v t)

typeDeclarationP :: Parser (Declaration ())
typeDeclarationP = do
  v <- typeIdentifierName
  _ <- symbol ":="
  t <- typeSchemeP
  return (TypDecl v t)

-- Multiple definitions seperated by ';'. Later definition may depend on earlier ones
environmentP :: Parser Syntax.Program.Environment
environmentP = (eof >> ask) <|> do
  decl <- sc >> declarationP
  local (insertDecl decl) environmentP

---------------------------------------------------------------------------------
-- Parsing for Repl
---------------------------------------------------------------------------------

bindingP :: Parser (FreeVarName, Term Prd ())
bindingP = do
  v <- typeIdentifierName
  _ <- lexeme (symbol "<-")
  t <- lexeme (termP PrdRep)
  return (v,t)

subtypingProblemP :: Parser (TypeScheme, TypeScheme)
subtypingProblemP = do
  t1 <- typeSchemeP
  _ <- symbol "<:"
  t2 <- typeSchemeP
  return (t1, t2)

---------------------------------------------------------------------------------
-- Type parsing
---------------------------------------------------------------------------------

-- ReaderT to keep track of recursively bound type variables
-- StateT to keep track of free type variables.
type TypeParser a = StateT (Set TVar) (ReaderT (Set RVar) (ReaderT Syntax.Program.Environment (Parsec Void String))) a

typeSchemeP :: Parser TypeScheme
typeSchemeP = do
  tvars <- option [] (symbol "forall" >> some (MkTVar <$> freeVarName) <* dot)
  (monotype, newtvars) <- runReaderT (runStateT typeR (S.fromList tvars)) S.empty
  return (TypeScheme (nub (tvars ++ S.toList newtvars)) monotype)

--without joins and meets
typeR' :: TypeParser TargetType
typeR' = try (parens typeR) <|>
  dataType <|>
  codataType <|>
  try recVar <|>
  try (typeEnvItem) <|>
  recType <|>
  typeVariable

typeR :: TypeParser TargetType
typeR = try joinType <|> try meetType <|> typeR'

dataType :: TypeParser TargetType
dataType = angles $ do
  xtorSigs <- xtorSignature `sepBy` pipe
  return (TTySimple Data xtorSigs)

codataType :: TypeParser TargetType
codataType = braces $ do
  xtorSigs <- xtorSignature `sepBy` comma
  return (TTySimple Codata xtorSigs)

xtorSignature :: TypeParser (XtorSig TargetType)
xtorSignature = do
  xt <- xtorName Structural
  args <- argListP (lexeme typeR) (lexeme typeR)
  return (MkXtorSig xt args)

recVar :: TypeParser TargetType
recVar = do
  rvs <- ask
  rv <- MkRVar <$> freeVarName
  guard (rv `S.member` rvs)
  return $ TTyRVar rv

typeVariable :: TypeParser TargetType
typeVariable = do
  tvs <- get
  tv <- MkTVar <$> freeVarName
  guard (tv `S.member` tvs)
  return $ TTyTVar tv

envItem :: Parser TypeScheme
envItem = do
  v <- lexeme (many alphaNumChar)
  env <- asks typEnv
  Just x <- return $ M.lookup v env
  return x

typeEnvItem :: TypeParser TargetType
typeEnvItem = do
  tvs <- S.toList <$> get
  TypeScheme newtvs ty <- alphaRenameTypeScheme tvs <$> lift (lift envItem)
  modify (S.union (S.fromList newtvs))
  return ty

joinType :: TypeParser TargetType
joinType = TTyUnion <$> (lexeme typeR' `sepBy2` (symbol "\\/"))

meetType :: TypeParser TargetType
meetType = TTyInter <$> (lexeme typeR' `sepBy2` (symbol "/\\"))

recType :: TypeParser TargetType
recType = do
  _ <- symbol "rec"
  rv <- MkRVar <$> freeVarName
  _ <- dot
  ty <- local (S.insert rv) typeR
  return $ TTyRec rv ty

---------------------------------------------------------------------------------
-- Nominal type declaration parser
---------------------------------------------------------------------------------

typeNameP :: Parser TypeName
typeNameP = MkTypeName <$> (lexeme $ (:) <$> upperChar <*> many alphaNumChar)


simpleTypeP :: Parser SimpleType
simpleTypeP = NominalType <$> typeNameP

dataDeclP :: Parser (Declaration ())
dataDeclP = DataDecl <$> dataDeclP'
  where
    dataDeclP' :: Parser DataDecl
    dataDeclP' = do
      dataCodata <- dataCodataDeclP
      tn <- typeNameP
      xtors <- braces $ xtorDeclP `sepBy` comma
      _ <- symbol ";"
      return NominalDecl
        { data_name = tn
        , data_polarity = dataCodata
        , data_xtors = xtors
        }

    dataCodataDeclP :: Parser DataCodata
    dataCodataDeclP = (symbol "data" >> return Data) <|> (symbol "codata" >> return Codata)

    xtorDeclP :: Parser (XtorSig SimpleType)
    xtorDeclP = do
      xt <- xtorName Nominal
      args <- argListP (lexeme simpleTypeP) (lexeme simpleTypeP)
      return (MkXtorSig xt args)



