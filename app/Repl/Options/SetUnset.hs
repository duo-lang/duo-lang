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


import Syntax.Kinds ( CallingConvention(CBN, CBV) )
import Repl.Repl
    ( Option(..),
      Repl,
      ReplInner,
      ReplState(evalOrder, typeInfOpts, steps, ReplState),
      EvalSteps(NoSteps, Steps),
      prettyRepl,
      mkWordCompleter )
import TypeInference.GenerateConstraints.Definition (InferenceMode(..))
import Utils (trim,  Verbosity(..))
import TypeInference.Driver

-- Set & Unset

setCmdVariants :: [(Text, Repl ())]
setCmdVariants = [ ("cbv", modify (\rs -> rs { evalOrder = CBV }))
                   , ("cbn", modify (\rs -> rs { evalOrder = CBN }))
                   , ("steps", modify (\rs -> rs { steps = Steps }))
                   , ("simplify", modify (\rs@ReplState { typeInfOpts } -> rs { typeInfOpts = typeInfOpts { infOptsSimplify = True } }))
                   , ("printGraphs", modify (\rs@ReplState { typeInfOpts } -> rs { typeInfOpts = typeInfOpts { infOptsPrintGraphs = True } }))
                   , ("verbose", modify (\rs@ReplState { typeInfOpts } -> rs { typeInfOpts = typeInfOpts {infOptsVerbosity = Verbose } }))
                   , ("silent", modify (\rs@ReplState { typeInfOpts } -> rs { typeInfOpts = typeInfOpts {infOptsVerbosity = Silent } }))
                   , ("refinements", modify (\rs@ReplState { typeInfOpts } -> rs { typeInfOpts = typeInfOpts { infOptsMode = InferRefined  } })) ]

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
                     , ("simplify", modify (\rs@ReplState { typeInfOpts } -> rs { typeInfOpts = typeInfOpts { infOptsSimplify = False } }))
                     , ("printGraphs", modify (\rs@ReplState { typeInfOpts } -> rs { typeInfOpts = typeInfOpts { infOptsPrintGraphs = False } }))
                     , ("refinements", modify (\rs@ReplState { typeInfOpts } -> rs { typeInfOpts = typeInfOpts { infOptsMode = InferNominal } }))]

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
