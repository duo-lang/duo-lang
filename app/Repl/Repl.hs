module Repl.Repl  where

import Control.Monad.Except (runExcept)
import Control.Monad.State
    ( gets, forM_, StateT, MonadIO(liftIO), modify )
import Data.Map qualified as M
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
import Driver.Definition
import Sugar.Desugar
import Translate.Focusing
import Utils (trimStr, defaultLoc)

------------------------------------------------------------------------------
-- Internal State of the Repl
------------------------------------------------------------------------------

data EvalSteps = Steps | NoSteps

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
  ds <- gets replDriverState
  inferredCmd <- liftIO $ inferProgramIO ds (MkModuleName "<Interactive>") [CST.CmdDecl defaultLoc Nothing (MkFreeVarName "main") comLoc]
  case inferredCmd of
    Right (_,[CmdDecl _ _ _ inferredCmd]) -> do
      env <- gets (drvEnv . replDriverState)
      steps <- gets steps
      let compiledCmd = focusCmd CBV (desugarCmd inferredCmd)
      let compiledEnv = focusEnvironment CBV (desugarEnvironment env)
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
