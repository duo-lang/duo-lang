module Parser.Parser
  ( runEnvParser
  , termP
  , commandP
  , declarationP
  , environmentP
  , typeSchemeP
  , subtypingProblemP
  , bindingP
  , Parser
  ) where

import Parser.Definition
import Parser.Lexer
import Parser.Program
import Parser.Terms
import Parser.Types
import Syntax.Terms
import Syntax.Types

---------------------------------------------------------------------------------
-- Parsing for Repl
---------------------------------------------------------------------------------

bindingP :: Parser (TypeName, Term Prd ())
bindingP = do
  v <- typeNameP
  _ <- lexeme (symbol "<-")
  t <- lexeme (termP PrdRep)
  return (v,t)

subtypingProblemP :: Parser (TypeScheme, TypeScheme)
subtypingProblemP = do
  t1 <- typeSchemeP
  _ <- symbol "<:"
  t2 <- typeSchemeP
  return (t1, t2)

