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

import Eval
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

xtorName :: (MonadParsec Void String m) => m XtorName
xtorName = MkXtorName <$> (lexeme $ (:) <$> upperChar <*> many alphaNumChar)

typeIdentifierName :: (MonadParsec Void String m) => m String
typeIdentifierName = lexeme $ (:) <$> upperChar <*> many alphaNumChar

dataOrCodata :: (MonadParsec Void String m) => m DataCodata
dataOrCodata = (symbol "+" >> return Data) <|> (symbol "-" >> return Codata)

parens, braces, brackets :: (MonadParsec Void String m) => m a -> m a
parens    = between (symbol "(") (symbol ")")
braces    = between (symbol "{") (symbol "}")
brackets  = between (symbol "[") (symbol "]")

comma, dot :: (MonadParsec Void String m) => m String
comma = symbol ","
dot = symbol "."

-- | Parse two lists, the first in parentheses and the second in brackets.
argListP :: (MonadParsec Void String m) => m a -> m a ->  m (Twice [a])
argListP p q = do
  xs <- option [] (parens   $ p `sepBy` comma)
  ys <- option [] (brackets $ q `sepBy` comma)
  return $ Twice xs ys

showDataCodata :: DataCodata -> String
showDataCodata Data = "+"
showDataCodata Codata = "-"

--------------------------------------------------------------------------------------------
-- Term/Command parsing
--------------------------------------------------------------------------------------------

--nice helper function for creating xtor signatures
argsSig :: Int -> Int -> Twice [()]
argsSig n m = Twice (replicate n ()) (replicate m ())

-- nice helper function for creating natural numbers
numToTerm :: Int -> Term Prd ()
numToTerm 0 = XtorCall Prd (MkXtorName "Z") (MkXtorArgs [] [])
numToTerm n = XtorCall Prd (MkXtorName "S") (MkXtorArgs [numToTerm (n-1)] [])

termEnvP :: PrdCns -> Parser (Term Prd ())
termEnvP Prd = do
  v <- lexeme (many alphaNumChar)
  prdEnv <- asks prdEnv
  Just t <- return $  M.lookup v prdEnv
  return t
termEnvP Cns = do
  v <- lexeme (many alphaNumChar)
  cnsEnv <- asks cnsEnv
  Just t <- return $ M.lookup v cnsEnv
  return t

termP :: PrdCns -> Parser (Term Prd ())
termP pc = try (parens (termP pc))
  <|> xtorCall pc
  <|> patternMatch pc
  <|> muAbstraction
  <|> try (termEnvP pc) -- needs to be tried, because the parser has to consume the string, before it checks
                        -- if the variable is in the environment, which might cause it to fail
  <|> freeVar pc
  <|> numLit
  <|> lambdaSugar

freeVar :: PrdCns -> Parser (Term Prd ())
freeVar pc = do
  v <- freeVarName
  return (FreeVar pc v ())

numLit :: Parser (Term Prd ())
numLit = numToTerm . read <$> some numberChar

lambdaSugar :: Parser (Term Prd ())
lambdaSugar = do
  _ <- lexeme (symbol "\\")
  args@(Twice prdVars cnsVars) <- argListP freeVarName freeVarName
  _ <- lexeme (symbol "=>")
  cmd <- lexeme commandP
  return $ Match Cns [MkCase (MkXtorName "Ap") (argsSig (length prdVars) (length cnsVars)) (commandClosing args cmd)]

xtorCall :: PrdCns -> Parser (Term Prd ())
xtorCall pc = do
  xt <- xtorName
  (Twice prdArgs cnsArgs) <- argListP (lexeme $ termP Prd) (lexeme $ termP Cns)
  return $ XtorCall pc xt (MkXtorArgs prdArgs cnsArgs)

patternMatch :: PrdCns -> Parser (Term Prd ())
patternMatch Prd = braces $ do -- Comatch!
  _ <- symbol "-"
  cases <- singleCase `sepBy` comma
  _ <- symbol "-"
  return $ Match Prd cases
patternMatch Cns = braces $ do -- Match!
  _ <- symbol "+"
  cases <- singleCase `sepBy` comma
  _ <- symbol "+"
  return $ Match Cns cases

singleCase :: Parser (Case ())
singleCase = do
  xt <- lexeme xtorName
  args@(Twice prdVars cnsVars) <- argListP freeVarName freeVarName
  _ <- symbol "=>"
  cmd <- lexeme commandP
  return MkCase { case_name = xt
                , case_args = argsSig (length prdVars) (length cnsVars)  -- e.g. X(x,y)[k] becomes X((),())[()]
                , case_cmd = commandClosing args cmd -- de brujin transformation
                }

muAbstraction :: Parser (Term Prd ())
muAbstraction = do
  pc <- muIdentifier
  v <- lexeme freeVarName
  _ <- dot
  cmd <- lexeme commandP
  return $ MuAbs pc () (commandClosingSingle pc v cmd)
  where muIdentifier = (symbol "mu*" >> return Prd) <|> (symbol "mu" >> return Cns)

commandP :: Parser (Command ())
commandP = try (parens commandP) <|> doneCmd <|> printCmd <|> applyCmd

applyCmd :: Parser (Command ())
applyCmd = do
  prd <- lexeme (termP Prd)
  _ <- lexeme (symbol ">>")
  cns <- lexeme (termP Cns)
  return (Apply prd cns)

doneCmd :: Parser (Command ())
doneCmd = lexeme (symbol "Done") >> return Done

printCmd :: Parser (Command ())
printCmd = lexeme (symbol "Print") >> (Print <$> lexeme (termP Prd))

---------------------------------------------------------------------------------
-- Parsing a program
---------------------------------------------------------------------------------

declarationP :: Parser (Declaration ())
declarationP = prdDeclarationP <|> cnsDeclarationP <|> typeDeclarationP

prdDeclarationP :: Parser (Declaration ())
prdDeclarationP = do
  _ <- try $ lexeme (symbol "prd")
  v <- freeVarName
  _ <- lexeme (symbol ":=")
  t <- lexeme (termP Prd)
  _ <- symbol ";"
  return (PrdDecl v t)

cnsDeclarationP :: Parser (Declaration ())
cnsDeclarationP = do
  _ <- try $ lexeme (symbol "cns")
  v <- freeVarName
  _ <- lexeme (symbol ":=")
  t <- lexeme (termP Cns)
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
  t <- lexeme (termP Prd)
  return (v,t)

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
  simpleType <|>
  try recVar <|>
  try (typeEnvItem) <|>
  recType <|>
  typeVariable

typeR :: TypeParser TargetType
typeR = try joinType <|> try meetType <|> typeR'

simpleType :: TypeParser TargetType
simpleType = braces $ do
  s <- dataOrCodata
  xtorSigs <- xtorSignature `sepBy` comma
  _ <- symbol (showDataCodata s)
  return $ TTySimple s xtorSigs

xtorSignature :: TypeParser (XtorSig TargetType)
xtorSignature = do
  xt <- xtorName
  args <- argListP (lexeme typeR) (lexeme typeR)
  return (xt, args)

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

subtypingProblemP :: Parser (TypeScheme, TypeScheme)
subtypingProblemP = do
  t1 <- typeSchemeP
  _ <- symbol "<:"
  t2 <- typeSchemeP
  return (t1, t2)
