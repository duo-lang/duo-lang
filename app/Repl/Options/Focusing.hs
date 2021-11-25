module Repl.Options.Focusing where

import Control.Monad.State ( gets )
import Data.Text (Text)
import Data.Map qualified as M

import Pretty.Pretty ( ppPrint )
import Repl.Repl 
import Translate.Focusing ( focusCmd )
import Translate.Desugar
import Syntax.Program

-- Static Focusing
focusingCmd :: Text -> Repl ()
focusingCmd s = do
  env <- gets (cmdEnv . replEnv)
  case M.lookup s env of
    Nothing -> prettyText "Cmd not declared in environment"
    Just (cmd,_) -> do
      evalOrder <- gets evalOrder
      let focusedCmd = focusCmd evalOrder (desugarCmd cmd)
      prettyText "Focused command:"
      prettyText (ppPrint focusedCmd)

focusOption :: Option
focusOption = Option
  { option_name = "focus"
  , option_cmd = focusingCmd
  , option_help = ["Enter a command and show the focused result. Uses the configured evaluation order for focusing."]
  , option_completer = Nothing
  }
