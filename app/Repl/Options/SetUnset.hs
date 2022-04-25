module Repl.Options.SetUnset
  ( setOption,
    unsetOption
  ) where

import Control.Monad.State ( modify )
import Data.List (isPrefixOf, intersperse)
import Data.Text (Text)
import Data.Text qualified as T
import System.Console.Haskeline.Completion
    ( simpleCompletion, CompletionFunc )

import Syntax.Common
import Repl.Repl
    ( Option(..),
      Repl,
      ReplInner,
      ReplState(..),
      EvalSteps(NoSteps, Steps),
      prettyRepl,
      mkWordCompleter )
import Utils (trim,  Verbosity(..))
import Driver.Driver


-- Set & Unset

modifyTypeInfOpts :: (InferenceOptions -> InferenceOptions) -> Repl ()
modifyTypeInfOpts f = modify (\rs@ReplState { replDriverState = ds@MkDriverState { driverOpts }} -> rs { replDriverState = ds { driverOpts = f driverOpts}})

setCmdVariants :: [(Text, Repl ())]
setCmdVariants = [ ("cbv", modify (\rs -> rs { evalOrder = CBV }))
                 , ("cbn", modify (\rs -> rs { evalOrder = CBN }))
                 , ("steps", modify (\rs -> rs { steps = Steps }))
                 , ("simplify", modifyTypeInfOpts (\f -> f { infOptsSimplify = True}))
                 , ("printGraphs", modifyTypeInfOpts (\f -> f { infOptsPrintGraphs = True }))
                 , ("verbose", modifyTypeInfOpts (\f -> f { infOptsVerbosity = Verbose }))
                 , ("silent", modifyTypeInfOpts (\f -> f { infOptsVerbosity = Silent }))
                 ]

setCmd :: Text -> Repl ()
setCmd s = do
  let s' = trim s
  case lookup s' setCmdVariants of
    Just action -> action
    Nothing -> do
      prettyRepl $ T.unlines [ "The option " <> s' <> " is not recognized."
                             , "Available options: " <> T.concat (intersperse ", " (fst <$> setCmdVariants))]

setCompleter :: CompletionFunc ReplInner
setCompleter = mkWordCompleter (x f)
  where
    f n = return $ filter (isPrefixOf n) (T.unpack . fst <$> setCmdVariants)
    x f word = f word >>= return . map simpleCompletion

unsetCompleter :: CompletionFunc ReplInner
unsetCompleter = mkWordCompleter (x f)
  where
    f n = return $ filter (isPrefixOf n) (T.unpack . fst <$> unsetCmdVariants)
    x f word = f word >>= return . map simpleCompletion

setOption :: Option
setOption = Option
  { option_name = "set"
  , option_cmd = setCmd
  , option_help = ["Set a Repl option."]
  , option_completer = Just setCompleter
  }

unsetCmdVariants :: [(Text, Repl ())]
unsetCmdVariants = [ ("steps", modify (\rs -> rs { steps = NoSteps }))
                   , ("simplify", modifyTypeInfOpts (\f -> f { infOptsSimplify = False }))
                   , ("printGraphs", modifyTypeInfOpts (\f -> f { infOptsPrintGraphs = False }))
                   ]

unsetCmd :: Text -> Repl ()
unsetCmd s = do
  let s' = trim s
  case lookup s' unsetCmdVariants of
    Just action -> action
    Nothing -> do
      prettyRepl $ T.unlines [ "The option " <> s' <> " is not recognized."
                             , "Available options: " <> T.concat (intersperse ", " (fst <$> unsetCmdVariants))]

unsetOption :: Option
unsetOption = Option
  { option_name = "unset"
  , option_cmd = unsetCmd
  , option_help = ["Unset a Repl option."]
  , option_completer = Just unsetCompleter
  }
