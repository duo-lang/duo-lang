module Repl.Options.Compile (compileOption) where

import Data.Text (Text)
import Text.Megaparsec ( errorBundlePretty )

import Parser.Parser ( termP, runInteractiveParser )
import Pretty.Pretty ( ppPrint )
import Repl.Repl ( prettyText, prettyRepl, Repl, Option(..) )
import Translate.Translate (compile)
import Syntax.CommonTerm ( PrdCnsRep(PrdRep) )

-- Compile

compileCmd :: Text -> Repl ()
compileCmd s = do
  case runInteractiveParser (termP PrdRep) s of
    Right (t, _pos) ->
      prettyText (" compile " <> ppPrint t <> "\n = " <> ppPrint (compile t))
    Left err2 -> do
      prettyText "Cannot parse as aterm:"
      prettyRepl (errorBundlePretty err2)

compileOption :: Option
compileOption = Option
  { option_name = "compile"
  , option_cmd = compileCmd
  , option_help = ["Enter a ATerm and show the translated STerm."]
  , option_completer = Nothing
  }
