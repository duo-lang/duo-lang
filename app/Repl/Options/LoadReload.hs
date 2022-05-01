module Repl.Options.LoadReload
  ( loadOption
  , reloadOption
  ) where

import Data.Text (Text)
import System.Console.Repline ( fileCompleter )

import Repl.Repl
    ( Option(..),
      Repl,
      runDriver,
      prettyText
    )

      
import Driver.Repl (load, reload)
import Utils (trim)

-- Load

loadCmd :: Text -> Repl ()
loadCmd txt = runDriver (load (trim txt))

loadOption :: Option
loadOption = Option
  { option_name = "load"
  , option_cmd = loadCmd
  , option_help = ["Load the given file from disk and add it to the environment."]
  , option_completer = Just fileCompleter
  }

-- Reload

reloadCmd :: Text -> Repl ()
reloadCmd "" = runDriver reload
reloadCmd _ = prettyText ":reload does not accept arguments"

reloadOption :: Option
reloadOption = Option
  { option_name = "reload"
  , option_cmd = reloadCmd
  , option_help = ["Reload all loaded files from disk."]
  , option_completer = Nothing
  }