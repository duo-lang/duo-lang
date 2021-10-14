module Repl.Options.Focusing where

import Data.Text (Text)
import Text.Megaparsec ( errorBundlePretty )

import Parser.Definition ( runInteractiveParser )
import Parser.STerms ( stermP )
import Pretty.Pretty ( ppPrint )
import Repl.Repl ( Option(..), Repl, prettyRepl, prettyText )
import Syntax.CommonTerm ( PrdCnsRep(PrdRep) )
import Translate.Focusing ( focusSTerm )

-- Static Focusing
focusingCmd :: Text -> Repl ()
focusingCmd s = do
  case runInteractiveParser (stermP PrdRep) s of
    Right (t, _pos) -> do
      prettyText "Unfocused term:"
      prettyText (ppPrint t)
      prettyText "Focused term:"
      prettyText (ppPrint (focusSTerm t))
    Left err2 -> do
      prettyText "Cannot parse as sterm:"
      prettyRepl (errorBundlePretty err2)

focusOption :: Option
focusOption = Option
  { option_name = "focus"
  , option_cmd = focusingCmd
  , option_help = ["Enter a STerm Prd and show the focused result."]
  , option_completer = Nothing
  }
