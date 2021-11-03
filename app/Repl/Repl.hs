module Repl.Repl  where

import Control.Monad.State
    ( gets, forM_, StateT, MonadIO(liftIO), modify )
import Data.Bifunctor (first)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.Console.Haskeline.Completion
    ( Completion, CompletionFunc, completeWord )
import System.Console.Repline ( HaskelineT, abort )
import System.IO.Error (tryIOError)

import Errors ()
import Eval.Eval ( runEval )
import Eval.STerms ( eval, evalSteps )
import Parser.Parser
    ( Parser, runFileParser, runInteractiveParser, commandP )
import Pretty.Errors ()
import Pretty.Pretty ( PrettyAnn, ppPrintIO )
import Pretty.Program ()
import Syntax.Program ( Environment )
import TypeInference.Driver
import Translate.Translate
import Utils (trimStr)
import Text.Megaparsec.Error (errorBundlePretty)

------------------------------------------------------------------------------
-- Internal State of the Repl
------------------------------------------------------------------------------

data EvalSteps = Steps | NoSteps

data Mode = Symmetric | Asymmetric

data ReplState = ReplState
  { replEnv :: Environment
  , loadedFiles :: [FilePath]
  , steps :: EvalSteps
  , mode :: Mode
  , typeInfOpts :: InferenceOptions
  }


initialReplState :: ReplState
initialReplState = ReplState { replEnv = mempty
                             , loadedFiles = []
                             , steps = NoSteps
                             , mode = Symmetric
                             , typeInfOpts = defaultInferenceOptions { infOptsLibPath = ["examples"] }
                             }

------------------------------------------------------------------------------
-- Repl Monad and helper functions
------------------------------------------------------------------------------

type ReplInner = StateT ReplState IO
type Repl a = HaskelineT ReplInner a

modifyEnvironment :: (Environment -> Environment) -> Repl ()
modifyEnvironment f = modify $ \rs@ReplState{..} -> rs { replEnv = f replEnv }

modifyLoadedFiles :: ([FilePath] -> [FilePath]) -> Repl ()
modifyLoadedFiles f = modify $ \rs@ReplState{..} -> rs { loadedFiles = f loadedFiles }

prettyRepl :: PrettyAnn a => a -> Repl ()
prettyRepl s = liftIO $ ppPrintIO s

prettyText :: Text -> Repl ()
prettyText = prettyRepl

fromRight :: PrettyAnn err => Either err b -> Repl b
fromRight (Right b) = return b
fromRight (Left err) = prettyRepl err >> abort

parseInteractive :: Parser a -> Text -> Repl a
parseInteractive p s = do
  fromRight (first (T.pack . errorBundlePretty) (runInteractiveParser p s))

parseFile :: FilePath -> Parser a -> Repl a
parseFile fp p = do
  s <- safeRead fp
  fromRight (first (T.pack . errorBundlePretty) (runFileParser fp p s))

safeRead :: FilePath -> Repl Text
safeRead file =  do
  let file' = trimStr file
  res <- liftIO $ tryIOError (T.readFile file')
  case res of
    (Left _) -> do
      liftIO $ putStrLn $ "File with name " ++ file' ++ " does not exist."
      abort
    (Right s) -> return $ s

------------------------------------------------------------------------------
-- Command
------------------------------------------------------------------------------

cmd :: String -> Repl ()
cmd s = do
  mode <- gets mode
  case mode of
    Symmetric  -> cmdSymmetric  (T.pack s)
    Asymmetric -> return ()


cmdSymmetric :: Text -> Repl ()
cmdSymmetric s = do
  (comLoc,_) <- parseInteractive commandP s
  let com = compileCmd comLoc
  env <- gets replEnv
  steps <- gets steps
  case steps of
    NoSteps -> do
      res <- fromRight $ runEval (eval com) env
      prettyRepl res
    Steps -> do
      res <- fromRight $ runEval (evalSteps com) env
      forM_ res (\cmd -> prettyRepl cmd >> prettyText "----")

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
