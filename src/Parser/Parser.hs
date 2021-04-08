module Parser.Parser
  ( runFileParser
  , runInteractiveParser
  , stermP
  , atermP
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
import Parser.ATerms
import Parser.STerms
import Parser.Types
import Syntax.Types

---------------------------------------------------------------------------------
-- Parsing for Repl
---------------------------------------------------------------------------------

subtypingProblemP :: Parser (TypeScheme Pos, TypeScheme Pos)
subtypingProblemP = do
  t1 <- typeSchemeP
  _ <- subtypeSym
  t2 <- typeSchemeP
  return (t1, t2)

