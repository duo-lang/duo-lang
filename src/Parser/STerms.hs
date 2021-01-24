module Parser.STerms
  ( termP
  , commandP
  )where

import Control.Monad.Reader
import qualified Data.Map as M
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char

import Eval.Substitution
import Parser.Definition
import Parser.Lexer
import Syntax.Program
import Syntax.STerms
import Utils

--------------------------------------------------------------------------------------------
-- Term/Command parsing
--------------------------------------------------------------------------------------------

--nice helper function for creating xtor signatures
argsSig :: Int -> Int -> Twice [()]
argsSig n m = Twice (replicate n ()) (replicate m ())

termEnvP :: PrdCnsRep pc -> Parser (STerm pc ())
termEnvP PrdRep = do
  v <- lexeme (many alphaNumChar)
  prdEnv <- asks (prdEnv . parseEnv)
  Just t <- return $  M.lookup v prdEnv
  return t
termEnvP CnsRep = do
  v <- lexeme (many alphaNumChar)
  cnsEnv <- asks (cnsEnv . parseEnv)
  Just t <- return $ M.lookup v cnsEnv
  return t

termP :: PrdCnsRep pc -> Parser (STerm pc ())
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

freeVar :: PrdCnsRep pc -> Parser (STerm pc ())
freeVar pc = do
  v <- freeVarName
  return (FreeVar pc v ())

numLit :: PrdCnsRep pc -> Parser (STerm pc ())
numLit CnsRep = empty
numLit PrdRep = numToTerm . read <$> some numberChar
  where
    numToTerm :: Int -> STerm Prd ()
    numToTerm 0 = XtorCall PrdRep (MkXtorName Structural "Z") (MkXtorArgs [] [])
    numToTerm n = XtorCall PrdRep (MkXtorName Structural "S") (MkXtorArgs [numToTerm (n-1)] [])

lambdaSugar :: PrdCnsRep pc -> Parser (STerm pc ())
lambdaSugar CnsRep = empty
lambdaSugar PrdRep= do
  _ <- lexeme (symbol "\\")
  args@(Twice prdVars cnsVars) <- argListP freeVarName freeVarName
  _ <- lexeme (symbol "=>")
  cmd <- lexeme commandP
  return $ XMatch PrdRep Structural [MkSCase (MkXtorName Structural "Ap") (argsSig (length prdVars) (length cnsVars)) (commandClosing args cmd)]

-- | Parse two lists, the first in parentheses and the second in brackets.
xtorArgsP :: Parser (XtorArgs ())
xtorArgsP = do
  xs <- option [] (parens   $ (termP PrdRep) `sepBy` comma)
  ys <- option [] (brackets $ (termP CnsRep) `sepBy` comma)
  return $ MkXtorArgs xs ys

xtorCall :: NominalStructural -> PrdCnsRep pc -> Parser (STerm pc ())
xtorCall ns pc = do
  xt <- xtorName ns
  args <- xtorArgsP
  return $ XtorCall pc xt args

patternMatch :: NominalStructural -> PrdCnsRep pc -> Parser (STerm pc ())
patternMatch ns PrdRep = do
  _ <- symbol "comatch"
  cases <- braces $ singleCase ns `sepBy` comma
  return $ XMatch PrdRep ns cases
patternMatch ns CnsRep = do
  _ <- symbol "match"
  cases <- braces $ singleCase ns `sepBy` comma
  return $ XMatch CnsRep ns cases

singleCase :: NominalStructural -> Parser (SCase ())
singleCase ns = do
  xt <- lexeme (xtorName ns)
  args@(Twice prdVars cnsVars) <- argListP freeVarName freeVarName
  _ <- symbol "=>"
  cmd <- lexeme commandP
  return MkSCase { scase_name = xt
                 , scase_args = argsSig (length prdVars) (length cnsVars)  -- e.g. X(x,y)[k] becomes X((),())[()]
                 , scase_cmd = commandClosing args cmd -- de brujin transformation
                 }

muAbstraction :: PrdCnsRep pc -> Parser (STerm pc ())
muAbstraction pc = do
  _ <- symbol (case pc of { PrdRep -> "mu"; CnsRep -> "mu*" })
  v <- lexeme freeVarName
  _ <- dot
  cmd <- lexeme commandP
  case pc of
    PrdRep -> return $ MuAbs pc () (commandClosingSingle CnsRep v cmd)
    CnsRep -> return $ MuAbs pc () (commandClosingSingle PrdRep v cmd)


cmdEnvP :: Parser (Command ())
cmdEnvP = do
  v <- lexeme (many alphaNumChar)
  prdEnv <- asks (cmdEnv . parseEnv)
  Just t <- return $  M.lookup v prdEnv
  return t

commandP :: Parser (Command ())
commandP = try (parens commandP) <|> try cmdEnvP <|> doneCmd <|> printCmd <|> applyCmd

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

