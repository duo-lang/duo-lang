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
import Syntax.AST.Types
import Syntax.Lowering.Types

---------------------------------------------------------------------------------
-- Parsing for Repl
---------------------------------------------------------------------------------

subtypingProblemP :: Parser (TypeScheme Pos, TypeScheme Pos)
subtypingProblemP = do
  t1 <- typeSchemeP
  _ <- subtypeSym
  t2 <- typeSchemeP
  case (lowerTypeScheme PosRep t1, lowerTypeScheme PosRep t2) of
    (Right res1, Right res2) -> pure (res1, res2)
    (_,_) -> fail "SubtypingProblemP: Cannot lower types."


