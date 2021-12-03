module Repl.Options.Quit (quitOption) where

import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import System.Exit (exitSuccess)

import Repl.Repl (Option(..), Repl)

quitCmd :: Text -> Repl ()
quitCmd _ = liftIO $ exitSuccess

quitOption :: Option
quitOption = Option
  { option_name = "quit"
  , option_cmd = quitCmd
  , option_help = ["Exit the Repl"]
  , option_completer = Nothing
  }