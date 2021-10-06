module Repl.Options.Subsume (subOption) where

import Data.Text (Text)

import Parser.Parser ( subtypingProblemP )
import Repl.Repl
    ( prettyRepl, Repl, Option(..), fromRight, parseInteractive )
import TypeAutomata.Subsume (subsume)

-- Subsume

subCmd :: Text -> Repl ()
subCmd s = do
  (t1,t2) <- parseInteractive subtypingProblemP s
  res <- fromRight (subsume t1 t2)
  prettyRepl res


subOption :: Option
subOption = Option
  { option_name = "sub"
  , option_cmd = subCmd
  , option_help = [ "Check whether subsumption holds between two types. E.g."
                  , "\":sub {+ True +} <: {+ True, False +}\""]
  , option_completer = Nothing
  }