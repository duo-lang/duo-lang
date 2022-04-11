module Repl.Repl  where

import Control.Monad.Except (runExcept)
import Control.Monad.State
    ( gets, forM_, StateT, MonadIO(liftIO), modify )
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import System.Console.Haskeline.Completion
    ( Completion, CompletionFunc, completeWord )
import System.Console.Repline ( HaskelineT, abort )
import System.IO.Error (tryIOError)

import Errors ()
import Eval.Eval ( eval, evalSteps )
import Parser.Parser
    ( Parser, runFileParser, runInteractiveParser, termP )
import Pretty.Errors ()
import Pretty.Pretty ( PrettyAnn, ppPrintIO )
import Pretty.Program ()
import Syntax.CST.Program qualified as CST
import Syntax.AST.Program ( Declaration(..) )
import Driver.Environment (Environment)
import Syntax.Common
import Driver.Driver
import Translate.Desugar
import Translate.Focusing
import Utils (trimStr, defaultLoc)

------------------------------------------------------------------------------
-- Internal State of the Repl
------------------------------------------------------------------------------

data EvalSteps = Steps | NoSteps

data ReplState = ReplState
  { replEnv :: Environment
  , loadedFiles :: [FilePath]
  , steps :: EvalSteps
  , evalOrder :: EvaluationOrder
  , typeInfOpts :: InferenceOptions
  }


initialReplState :: ReplState
initialReplState = ReplState { replEnv = mempty
                             , loadedFiles = []
                             , steps = NoSteps
                             , evalOrder = CBV
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
  fromRight (runExcept (runInteractiveParser p s))

parseFile :: FilePath -> Parser a -> Repl a
parseFile fp p = do
  s <- safeRead fp
  fromRight (runExcept (runFileParser fp p s))

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
  (comLoc,_) <- parseInteractive termP (T.pack s)
  oldEnv <- gets replEnv
  opts <- gets typeInfOpts
  inferredCmd <- liftIO $ inferProgramIO (DriverState opts oldEnv mempty) [CST.CmdDecl defaultLoc Nothing (MkFreeVarName "main") comLoc]
  case inferredCmd of
    Right (_,[CmdDecl _ _ _ inferredCmd]) -> do
      evalOrder <- gets evalOrder
      env <- gets replEnv
      steps <- gets steps
      let compiledCmd = focusCmd evalOrder (desugarCmd inferredCmd)
      let compiledEnv = focusEnvironment evalOrder (desugarEnvironment env)
      case steps of
        NoSteps -> do
          resE <- liftIO $ eval compiledCmd compiledEnv
          res <- fromRight resE
          prettyRepl res
        Steps -> do
          resE <- liftIO $ evalSteps compiledCmd compiledEnv
          res <- fromRight  resE
          forM_ res (\cmd -> prettyRepl cmd >> prettyText "----")
    Right _ -> prettyText "Unreachable"
    Left err -> prettyRepl err

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
