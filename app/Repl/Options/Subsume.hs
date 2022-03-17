module Repl.Options.Subsume (subOption) where

import Control.Monad.State
import Data.Text (Text)

import Parser.Parser ( subtypingProblemP )
import Repl.Repl
    ( prettyRepl, ReplState(..), Repl, Option(..), fromRight, parseInteractive )
import TypeAutomata.Subsume (subsume)
import Driver.Definition
import Syntax.Common
import Syntax.Lowering.Types

-- Subsume

subCmd :: Text -> Repl ()
subCmd s = do
  env <- gets replEnv
  opts <- gets typeInfOpts
  let ds = DriverState opts env
  (t1,t2) <- parseInteractive subtypingProblemP s
  t1' <- liftIO $ execDriverM ds mempty $ lowerTypeScheme PosRep t1
  t2' <- liftIO $ execDriverM ds mempty $ lowerTypeScheme PosRep t2
  case (t1', t2') of
     (Right (res1,_), Right (res2,_)) -> do
       res <- fromRight (subsume res1 res2)
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