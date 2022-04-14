module Repl.Options.Subsume (subOption) where

import Data.Text (Text)
import Data.Map qualified as M

import Parser.Parser ( subtypingProblemP )
import Repl.Repl
    ( prettyRepl, Repl, Option(..), fromRight, parseInteractive )
import TypeAutomata.Subsume (subsume)
import Renamer.Definition
import Renamer.Types
import Syntax.Common


-- Subsume

subCmd :: Text -> Repl ()
subCmd s = do
  (t1,t2) <- parseInteractive subtypingProblemP s
  let t1' = runRenamerM M.empty $ renameTypeScheme PosRep t1
  let t2' = runRenamerM M.empty $ renameTypeScheme PosRep t2
  case (t1', t2') of
     (Right res1, Right res2) -> do
       res <- fromRight (subsume PosRep res1 res2)
       prettyRepl res
     (_,_) -> fail "SubtypingProblemP: Cannot lower types."

  


subOption :: Option
subOption = Option
  { option_name = "sub"
  , option_cmd = subCmd
  , option_help = [ "Check whether subsumption holds between two types. E.g."
                  , "\":sub {+ True +} <: {+ True, False +}\""]
  , option_completer = Nothing
  }