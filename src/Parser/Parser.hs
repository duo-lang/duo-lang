module Parser.Parser
  ( runEnvParser
  , stermP
  , atermP
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
import Parser.ATerms
import Parser.STerms
import Parser.Types
import Syntax.STerms
import Syntax.Types

---------------------------------------------------------------------------------
-- Parsing for Repl
---------------------------------------------------------------------------------

bindingP :: Parser (TypeName, STerm Prd ())
bindingP = do
  v <- typeNameP
  _ <- lexeme (symbol "<-")
  t <- lexeme (stermP PrdRep)
  return (v,t)

subtypingProblemP :: Parser (TypeScheme, TypeScheme)
subtypingProblemP = do
  t1 <- typeSchemeP
  _ <- symbol "<:"
  t2 <- typeSchemeP
  return (t1, t2)

