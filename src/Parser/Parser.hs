module Parser.Parser
  ( runFileParser
  , runInteractiveParser
  , termP
  , commandP
  , declarationP
  , programP
  , typeSchemeP
  , subtypingProblemP
  , Parser
  ) where

import Parser.Definition
import Parser.Lexer
import Parser.Program
import Parser.Terms
import Parser.Types
import Syntax.CST.Types

---------------------------------------------------------------------------------
-- Parsing for Repl
---------------------------------------------------------------------------------

subtypingProblemP :: Parser (TypeScheme, TypeScheme)
subtypingProblemP = do
  t1 <- typeSchemeP
  _ <- subtypeSym
  t2 <- typeSchemeP
  return (t1,t2)

