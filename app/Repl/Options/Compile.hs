module Repl.Options.Compile (compileOption) where

import Control.Monad.State ( gets )
import Data.Map qualified as M
import Data.Text (Text)

import Pretty.Pretty ( ppPrint )
import Translate.Desugar (compile)
import Syntax.Program 
import Repl.Repl

-- Compile

compileCmd :: Text -> Repl ()
compileCmd s = do
  env <- gets (prdEnv . replEnv)
  case M.lookup s env of
    Nothing -> prettyText "Producer not declared in environment"
    Just (prd,_,_) -> do
      let compiledPrd = compile prd
      prettyText "Compiled Producer:"
      prettyText (ppPrint compiledPrd)

compileOption :: Option
compileOption = Option
  { option_name = "compile"
  , option_cmd = compileCmd
  , option_help = ["Enter a ATerm and show the translated STerm."]
  , option_completer = Nothing
  }
