module Repl.Options.Let (letOption) where

import Data.Text (Text)

import Driver.Repl (letRepl)

import Repl.Repl
    ( Repl,
      runDriver,
      Option(..),
    )


letCmd :: Text -> Repl ()
letCmd txt = runDriver (letRepl txt)
  
letOption :: Option
letOption = Option
  { option_name = "let"
  , option_cmd = letCmd
  , option_help = [ "Add a declaration to the current environment. E.g."
                  , "\":let prd myTrue := {- Ap(x)[y] => x >> y -};\""]
  , option_completer = Nothing
  }
