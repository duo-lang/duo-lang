module Repl.Repl  where

import Control.Monad.State
    ( gets, StateT, MonadIO(liftIO), modify )
import Data.Map qualified as M
import Data.Text (Text)
import Data.Text qualified as T
import System.Console.Haskeline.Completion
    ( Completion, CompletionFunc, completeWord )
import System.Console.Repline ( HaskelineT, abort )

import Errors ()
import Pretty.Errors ()
import Pretty.Pretty ( PrettyAnn, ppPrintIO )
import Pretty.Program ()
import Driver.Environment (Environment)
import Syntax.Common
import Driver.Driver
import Driver.Repl (runCmd, EvalSteps(..))
import Driver.Definition ( DriverM, defaultDriverState )


------------------------------------------------------------------------------
-- Internal State of the Repl
------------------------------------------------------------------------------

data ReplState = ReplState
  { replDriverState :: DriverState
  , steps :: EvalSteps
  }


initialReplState :: ReplState
initialReplState = ReplState { replDriverState = defaultDriverState
                             , steps = NoSteps
                             }

------------------------------------------------------------------------------
-- Repl Monad and helper functions
------------------------------------------------------------------------------

type ReplInner = StateT ReplState IO
type Repl a = HaskelineT ReplInner a

modifyEnvironment :: ModuleName -> (Environment -> Environment) -> Repl ()
modifyEnvironment mn f = modify g
  where
    g rs@ReplState{ replDriverState = ds@MkDriverState { drvEnv }} = rs { replDriverState = ds { drvEnv = M.adjust f mn drvEnv } }

prettyRepl :: PrettyAnn a => a -> Repl ()
prettyRepl s = liftIO $ ppPrintIO s

prettyText :: Text -> Repl ()
prettyText = prettyRepl

fromRight :: PrettyAnn err => Either err b -> Repl b
fromRight (Right b) = return b
fromRight (Left err) = prettyRepl err >> abort

runDriver :: DriverM a -> Repl a
runDriver act = do
  ds <- gets replDriverState
  (res, warnings) <- liftIO $ execDriverM ds act
  mapM_ prettyRepl warnings
  case res of
    Left errs -> do
      mapM_ prettyRepl errs
      abort
    Right (res, ds') -> do
      modify (\rs  -> rs { replDriverState = ds' })
      pure res


------------------------------------------------------------------------------
-- Command
------------------------------------------------------------------------------

cmd :: String -> Repl ()
cmd txt = do
  steps <- gets steps
  runDriver (runCmd (T.pack txt) steps)

------------------------------------------------------------------------------
-- Options
------------------------------------------------------------------------------

data Option = Option
  { option_name :: Text
  , option_cmd  :: Text -> Repl ()
  , option_help :: [Text]
  , option_completer :: Maybe (CompletionFunc ReplInner)
  }

mkWordCompleter :: Monad m =>  (String -> m [Completion]) -> CompletionFunc m
mkWordCompleter = completeWord (Just '\\') " \t()[]"
