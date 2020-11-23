{-# LANGUAGE FlexibleContexts #-}

module Parser
  ( runEnvParser , termP, commandP, definitionP, environmentP, typeSchemeP, typeDefinitionP, subtypingProblemP, bindingP )
  where

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Reader

import Data.Void
import Data.Bifunctor

import Eval
import Syntax

-- A parser that can read values from an environment
type EnvParser e = ReaderT (Map String e) (Parsec Void String)

runEnvParser :: EnvParser e a -> Environment e -> String -> Either Error a
runEnvParser p env input = case runParser (runReaderT (lexeme (p <* eof)) env) "<interactive>" input of
  Left err -> Left $ ParseError (errorBundlePretty err)
  Right x -> Right x

-------------------------------------------------------------------------------------------
-- Generic Parsers
-------------------------------------------------------------------------------------------

sepBy2 :: MonadPlus m => m a -> m sep -> m [a]
sepBy2 p sep = (:) <$> (p <* sep) <*> (sepBy1 p sep)

envItem :: EnvParser e e
envItem = do
  v <- lexeme (many alphaNumChar)
  Just x <- M.lookup v <$> ask
  return x

sc :: (MonadParsec Void String m) => m ()
sc = L.space space1 (L.skipLineComment "#") (L.skipBlockComment "###" "###")

lexeme :: (MonadParsec Void String m) => m a -> m a
lexeme = L.lexeme sc

symbol :: (MonadParsec Void String m) => String -> m String
symbol = L.symbol sc

freeVarName :: (MonadParsec Void String m) => m FreeVarName
freeVarName = lexeme $ ((:) <$> lowerChar <*> many alphaNumChar) <|> symbol "_"

xtorName :: (MonadParsec Void String m) => m XtorName
xtorName = lexeme $ (:) <$> upperChar <*> many alphaNumChar

typeIdentifierName :: (MonadParsec Void String m) => m XtorName
typeIdentifierName = lexeme $ (:) <$> upperChar <*> many alphaNumChar

dataOrCodata :: (MonadParsec Void String m) => m DataOrCodata
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

--------------------------------------------------------------------------------------------
-- Term/Command parsing
--------------------------------------------------------------------------------------------

type TermParser a = EnvParser (Term ()) a

--nice helper function for creating xtor signatures
argsSig :: Int -> Int -> Twice [()]
argsSig n m = Twice (replicate n ()) (replicate m ())

-- nice helper function for creating natural numbers
numToTerm :: Int -> Term ()
numToTerm 0 = XtorCall Data "Z" (Twice [] [])
numToTerm n = XtorCall Data "S" (Twice [numToTerm (n-1)] [])

termP :: PrdOrCns -> TermParser (Term ())
termP mode = try (parens (termP mode))
  <|> xtorCall mode
  <|> patternMatch
  <|> muAbstraction
  <|> try envItem -- needs to be tried, because the parser has to consume the string, before it checks
                  -- if the variable is in the environment, which might cause it to fail
  <|> freeVar
  <|> numLit

freeVar :: TermParser (Term ())
freeVar = do
  v <- freeVarName
  return (FreeVar v ())

numLit :: TermParser (Term ())
numLit = numToTerm . read <$> some numberChar

xtorCall :: PrdOrCns -> TermParser (Term ())
xtorCall mode = do
  xt <- xtorName
  args <- argListP (lexeme $ termP Prd) (lexeme $ termP Cns)
  return $ XtorCall (case mode of { Prd -> Data ; Cns -> Codata }) xt args

patternMatch :: TermParser (Term ())
patternMatch = braces $ do
  s <- dataOrCodata
  cases <- singleCase `sepBy` comma
  _ <- symbol (showDataOrCodata s)
  return $ Match s cases

singleCase :: TermParser (MatchCase ())
singleCase = do
  xt <- lexeme xtorName
  args@(Twice prdVars cnsVars) <- argListP freeVarName freeVarName
  _ <- symbol "=>"
  cmd <- lexeme commandP
  return (xt,
          argsSig (length prdVars) (length cnsVars),  -- e.g. X(x,y)[k] becomes X((),())[()]
          commandClosing args cmd) -- de brujin transformation

muAbstraction :: TermParser (Term ())
muAbstraction = do
  pc <- muIdentifier
  v <- lexeme freeVarName
  _ <- dot
  cmd <- lexeme commandP
  return $ MuAbs pc () (commandClosingSingle pc v cmd)
  where muIdentifier = (symbol "mu*" >> return Prd) <|> (symbol "mu" >> return Cns)

commandP :: TermParser (Command ())
commandP = try (parens commandP) <|> doneCmd <|> printCmd <|> applyCmd

applyCmd :: TermParser (Command ())
applyCmd = do
  prd <- lexeme (termP Prd)
  _ <- lexeme (symbol ">>")
  cns <- lexeme (termP Cns)
  return (Apply prd cns)

doneCmd :: TermParser (Command ())
doneCmd = lexeme (symbol "Done") >> return Done

printCmd :: TermParser (Command ())
printCmd = lexeme (symbol "Print") >> (Print <$> lexeme (termP Prd))


definitionP :: TermParser (FreeVarName, Term ())
definitionP = prdDefinitionP <|> cnsDefinitionP

prdDefinitionP :: TermParser (FreeVarName, Term ())
prdDefinitionP = do
  _ <- try $ lexeme (symbol "prd")
  v <- freeVarName
  _ <- lexeme (symbol ":=")
  t <- lexeme (termP Prd)
  return (v,t)

cnsDefinitionP :: TermParser (FreeVarName, Term ())
cnsDefinitionP = do
  _ <- try $ lexeme (symbol "cns")
  v <- freeVarName
  _ <- lexeme (symbol ":=")
  t <- lexeme (termP Cns)
  return (v,t)


-- multuple definitions seperated by ';'. Later definition may depend on earlier ones
environmentP :: TermParser TermEnvironment
environmentP = (eof >> ask) <|> do
  (v,t) <- sc >> definitionP
  _ <- symbol ";"
  local (M.insert v t) environmentP

bindingP :: TermParser (FreeVarName, Term ())
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
type TypeParser a = StateT (Set TVar) (ReaderT (Set RVar) (EnvParser TypeScheme)) a

typeSchemeP :: EnvParser TypeScheme TypeScheme
typeSchemeP = do
  tvars <- option [] (symbol "forall" >> some (MkTVar <$> freeVarName) <* dot)
  (monotype, newtvars) <- runReaderT (runStateT typeR (S.fromList tvars)) S.empty
  return (TypeScheme (tvars ++ S.toList newtvars) monotype)

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
  _ <- symbol (showDataOrCodata s)
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

typeDefinitionP :: EnvParser TypeScheme (TypeIdentifierName, TypeScheme)
typeDefinitionP = do
  v <- typeIdentifierName
  _ <- symbol ":="
  t <- typeSchemeP
  return (v,t)

subtypingProblemP :: EnvParser TypeScheme (TypeScheme, TypeScheme)
subtypingProblemP = do
  t1 <- typeSchemeP
  _ <- symbol "<:"
  t2 <- typeSchemeP
  return (t1, t2)
