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
import Syntax.Types

---------------------------------------------------------------------------------
-- Parsing for Repl
---------------------------------------------------------------------------------

subtypingProblemP :: Parser (TypeScheme Pos, TypeScheme Pos)
subtypingProblemP = do
  t1 <- typeSchemeP PosRep
  _ <- subtypeSym
  t2 <- typeSchemeP PosRep
  return (t1, t2)

