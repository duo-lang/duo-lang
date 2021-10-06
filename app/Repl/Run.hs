module Repl.Run (runRepl) where

import Control.Monad.Reader ( forM_ )
import Control.Monad.State ( gets, StateT(runStateT) )
import Data.List (isPrefixOf)
import qualified Data.Map as M
import Data.Maybe (catMaybes)
import Data.Text (Text)
import qualified Data.Text as T
import System.Console.Haskeline.Completion
    ( simpleCompletion, CompletionFunc )
import System.Console.Repline
    ( dontCrash,
      evalReplOpts,
      CompleterStyle(Prefix),
      ExitDecision(Exit),
      ReplOpts(..) )

import Repl.Options.Let (letOption)
import Repl.Options.Simplify (simplifyOption)
import Repl.Options.Subsume (subOption)
import Repl.Options.Compile (compileOption)
import Repl.Options.LoadReload (loadOption, reloadOption)
import Repl.Options.Show (showOption, showTypeOption)      
import Repl.Options.SetUnset (setOption, unsetOption)
import Repl.Options.SaveGraphs (saveOption)
import Repl.Repl
    ( Option(..),
      Repl,
      ReplInner,
      ReplState(loadedFiles, replEnv),
      initialReplState,
      mkWordCompleter,
      prettyRepl,
      prettyText,
      cmd )
import Syntax.Program
    ( Environment(prdEnv, cnsEnv, cmdEnv, defEnv, declEnv) )
import Syntax.Types ( DataDecl(data_name), TypeName(unTypeName) )

------------------------------------------------------------------------------
-- Options
------------------------------------------------------------------------------

-- All Options
allOptions :: [Option]
allOptions =
  [ showOption
  , helpOption
  , letOption
  , saveOption
  , setOption
  , unsetOption
  , subOption
  , simplifyOption
  , compileOption
  , loadOption
  , reloadOption
  , showTypeOption
  ]

-- Help
helpCmd :: Text -> Repl ()
helpCmd _ = do
  prettyText "Available commands:\n"
  forM_ allOptions (\opt -> showHelp (option_name opt) (option_help opt))
  where
    showHelp :: Text -> [Text] -> Repl ()
    showHelp name help = do
      prettyRepl $ ":" <> name
      forM_ help (\help -> prettyRepl $ "    " <> help)

helpOption :: Option
helpOption = Option
  { option_name = "help"
  , option_cmd = helpCmd
  , option_help = ["Show all available commands."]
  , option_completer = Nothing
  }

------------------------------------------------------------------------------
-- Repl Configuration
------------------------------------------------------------------------------

ini :: Repl ()
ini = do
  prettyRepl $ unlines [ "DualSub: Algebraic subtyping for data and codata."
                       , "Press Ctrl+D to exit."
                       , "Enter :help for a list of available commands."
                       ]
  (option_cmd reloadOption) ""

final :: Repl ExitDecision
final = prettyText "Goodbye!" >> return Exit

replBanner :: a -> Repl String
replBanner _ = do
  loadedFiles <- gets loadedFiles
  pure (unwords loadedFiles ++ ">")

opts :: ReplOpts ReplInner
opts = ReplOpts
  { banner           = replBanner
  , command          = cmd
  , options          = (\opt -> (T.unpack (option_name opt), \s -> dontCrash ((option_cmd opt) (T.pack s)))) <$> allOptions
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
      let completionList = (':' :) . T.unpack . option_name <$> allOptions
      let keys = concat [ M.keys (prdEnv env)
                        , M.keys (cnsEnv env)
                        , M.keys (cmdEnv env)
                        , M.keys (defEnv env)
                        , (unTypeName . data_name) <$> (declEnv env)
                        ]
      return $ filter (isPrefixOf n) (completionList ++ (T.unpack <$> keys))
    _simpleComplete f word = f word >>= return . map simpleCompletion


prefixCompleters :: [(String, CompletionFunc ReplInner)]
prefixCompleters = catMaybes (mkCompleter <$> allOptions)
  where
    mkCompleter Option { option_completer = Nothing } = Nothing
    mkCompleter Option { option_name = name, option_completer = Just completer } = Just (':' : T.unpack name, completer)

------------------------------------------------------------------------------
-- Run the Repl
------------------------------------------------------------------------------

runRepl :: IO ()
runRepl = runStateT (evalReplOpts opts) initialReplState >> return ()
