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
import Eval.Eval ( EvalOrder(CBV), runEval )
import Eval.ATerms ( evalATermComplete, evalATermSteps )
import Eval.STerms ( eval, evalSteps )
import Parser.Parser
    ( Parser, atermP, runFileParser, runInteractiveParser, commandP )
import Pretty.Errors ()
import Pretty.Pretty ( PrettyAnn, ppPrintIO )
import Pretty.Program ()
import Syntax.Program ( Environment )
import Syntax.STerms ( FreeVarName )
import TypeInference.GenerateConstraints.Definition (InferenceMode(..))
import Utils (trimStr, Verbosity(..))
import Text.Megaparsec.Error (errorBundlePretty)

------------------------------------------------------------------------------
-- Internal State of the Repl
------------------------------------------------------------------------------

data EvalSteps = Steps | NoSteps

data Mode = Symmetric | Asymmetric

data ReplState = ReplState
  { replEnv :: Environment FreeVarName
  , loadedFiles :: [FilePath]
  , steps :: EvalSteps
  , evalOrder :: EvalOrder
  , mode :: Mode
  , typeInfVerbosity :: Verbosity
  , inferenceMode :: InferenceMode
  }


initialReplState :: ReplState
initialReplState = ReplState { replEnv = mempty
                             , loadedFiles = []
                             , steps = NoSteps
                             , evalOrder = CBV
                             , mode = Symmetric
                             , typeInfVerbosity = Silent
                             , inferenceMode = InferNominal
                             }

------------------------------------------------------------------------------
-- Repl Monad and helper functions
------------------------------------------------------------------------------

type ReplInner = StateT ReplState IO
type Repl a = HaskelineT ReplInner a

modifyEnvironment :: (Environment FreeVarName -> Environment FreeVarName) -> Repl ()
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
    Asymmetric -> cmdAsymmetric (T.pack s)


cmdSymmetric :: Text -> Repl ()
cmdSymmetric s = do
  (comLoc,_) <- parseInteractive commandP s
  let com = first (const ()) comLoc
  evalOrder <- gets evalOrder
  env <- gets replEnv
  steps <- gets steps
  case steps of
    NoSteps -> do
      res <- fromRight $ runEval (eval com) evalOrder env
      prettyRepl res
    Steps -> do
      res <- fromRight $ runEval (evalSteps com) evalOrder env
      forM_ res (\cmd -> prettyRepl cmd >> prettyText "----")

cmdAsymmetric :: Text -> Repl ()
cmdAsymmetric s = do
  (tmLoc,_) <- parseInteractive atermP s
  let tm = first (const ()) tmLoc
  evalOrder <- gets evalOrder
  env <- gets replEnv
  steps <- gets steps
  case steps of
    NoSteps -> do
      let res = runEval (evalATermComplete tm) evalOrder env
      case res of
        Left error -> prettyRepl error
        Right res' -> prettyRepl res'
    Steps -> do
      res <- fromRight $ runEval (evalATermSteps tm) evalOrder env
      forM_ res (\t -> prettyRepl t >> prettyText "----")

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