module Repl.Options.Focusing where

import Control.Monad.State ( gets )
import Data.Text (Text)
import Text.Megaparsec ( errorBundlePretty )

import Parser.Definition ( runInteractiveParser )
import Parser.Terms ( commandP )
import Pretty.Pretty ( ppPrint )
import Repl.Repl ( Option(..), Repl, prettyRepl, prettyText, evalOrder )
import Translate.Focusing ( focusCmd )

-- Static Focusing
focusingCmd :: Text -> Repl ()
focusingCmd s = do
  evalOrder <- gets evalOrder
  case runInteractiveParser commandP s of
    Right (t, _pos) -> do
      prettyText "Unfocused term:"
      prettyText (ppPrint t)
      prettyText "Focused term:"
      prettyText (ppPrint (focusCmd evalOrder t))
    Left err2 -> do
      prettyText "Cannot parse as command:"
      prettyRepl (errorBundlePretty err2)

focusOption :: Option
focusOption = Option
  { option_name = "focus"
  , option_cmd = focusingCmd
  , option_help = ["Enter a command and show the focused result. Uses the configured evaluation order for focusing."]
  , option_completer = Nothing
  }
