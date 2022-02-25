module Repl.Options.Subsume (subOption) where

import Data.Text (Text)

import Parser.Parser ( subtypingProblemP )
import Repl.Repl
    ( prettyRepl, Repl, Option(..), fromRight, parseInteractive )
import TypeAutomata.Subsume (subsume)
import Syntax.Lowering.Lowering
import Syntax.Lowering.Types
import Syntax.AST.Types

-- Subsume

subCmd :: Text -> Repl ()
subCmd s = do
  (t1,t2) <- parseInteractive subtypingProblemP s
  case (runLowerM $ lowerTypeScheme PosRep t1, runLowerM $ lowerTypeScheme PosRep t2) of
     (Right res1, Right res2) -> do
       res <- fromRight (subsume res1 res2)
       prettyRepl res
     (_,_) -> fail "SubtypingProblemP: Cannot lower types."

  


subOption :: Option
subOption = Option
  { option_name = "sub"
  , option_cmd = subCmd
  , option_help = [ "Check whether subsumption holds between two types. E.g."
                  , "\":sub {+ True +} <: {+ True, False +}\""]
  , option_completer = Nothing
  }