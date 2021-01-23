module Parser.Parser
  ( runEnvParser , termP, commandP, declarationP, environmentP, typeSchemeP, subtypingProblemP, bindingP, Parser)
  where



import Syntax.Terms
import Syntax.Types

import Parser.Definition
import Parser.Lexer
import Parser.Terms
import Parser.Types
import Parser.Program



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


