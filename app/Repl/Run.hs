module Repl.Run where

import System.Console.Repline hiding (Command)
import System.Console.Haskeline.Completion
import Control.Monad.Reader
import Control.Monad.State
import Data.List (isPrefixOf)
import qualified Data.Map as M
import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Text as T

import Repl.Options
import Repl.Repl
import Syntax.Program
import Syntax.Types


-- All Options
all_options :: [Option]
all_options = [ show_option, help_option, let_option, save_option, set_option, unset_option
              , sub_option, simplify_option, compile_option, load_option, reload_option, show_type_option]

              -- Help

help_cmd :: Text -> Repl ()
help_cmd _ = do
  prettyText "Available commands:\n"
  forM_ all_options (\opt -> showHelp (option_name opt) (option_help opt))
  where
    showHelp :: Text -> [Text] -> Repl ()
    showHelp name help = do
      prettyRepl $ ":" <> name
      forM_ help (\help -> prettyRepl $ "    " <> help)

help_option :: Option
help_option = Option
  { option_name = "help"
  , option_cmd = help_cmd
  , option_help = ["Show all available commands."]
  , option_completer = Nothing
  }

ini :: Repl ()
ini = do
  prettyRepl $ unlines [ "DualSub: Algebraic subtyping for data and codata."
                       , "Press Ctrl+D to exit."
                       , "Enter :help for a list of available commands."
                       ]
  reload_cmd ""

final :: Repl ExitDecision
final = prettyText "Goodbye!" >> return Exit

repl_banner :: a -> Repl String
repl_banner _ = do
  loadedFiles <- gets loadedFiles
  pure (unwords loadedFiles ++ ">")

opts :: ReplOpts ReplInner
opts = ReplOpts
  { banner           = repl_banner
  , command          = cmd
  , options          = (\opt -> (T.unpack (option_name opt), \s -> dontCrash ((option_cmd opt) (T.pack s)))) <$> all_options
  , prefix           = Just ':'
  , multilineCommand = Nothing
  , tabComplete      = newCompleter
  , initialiser      = ini
  , finaliser        = final
  }


newCompleter :: CompleterStyle ReplInner
newCompleter = Prefix cmdCompleter prefixCompleters

cmdCompleter :: CompletionFunc ReplInner
cmdCompleter = mkWordCompleter (_simpleComplete f)
  where
    f n = do
      env <- gets replEnv
      let completionList = (':' :) . T.unpack . option_name <$> all_options
      let keys = concat [ M.keys (prdEnv env)
                        , M.keys (cnsEnv env)
                        , M.keys (cmdEnv env)
                        , M.keys (defEnv env)
                        , (unTypeName . data_name) <$> (declEnv env)
                        ]
      return $ filter (isPrefixOf n) (completionList ++ (T.unpack <$> keys))
    _simpleComplete f word = f word >>= return . map simpleCompletion


prefixCompleters :: [(String, CompletionFunc ReplInner)]
prefixCompleters = catMaybes (mkCompleter <$> all_options)
  where
    mkCompleter Option { option_completer = Nothing } = Nothing
    mkCompleter Option { option_name = name, option_completer = Just completer } = Just (':' : T.unpack name, completer)
------------------------------------------------------------------------------
-- Run the Repl
------------------------------------------------------------------------------

runRepl :: IO ()
runRepl = runStateT (evalReplOpts opts) initialReplState >> return ()
