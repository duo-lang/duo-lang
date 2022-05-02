module Repl.Options.Subsume (subOption) where

import Data.Text (Text)

import Driver.Repl (subsumeRepl)
import Repl.Repl  ( Repl, Option(..), runDriver)

-- Subsume

subCmd :: Text -> Repl ()
subCmd s = runDriver (subsumeRepl s)

subOption :: Option
subOption = Option
  { option_name = "sub"
  , option_cmd = subCmd
  , option_help = [ "Check whether subsumption holds between two types. E.g."
                  , "\":sub {+ True +} <: {+ True, False +}\""]
  , option_completer = Nothing
  }