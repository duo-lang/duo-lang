module Repl.Options.LoadReload
  ( loadOption
  , reloadOption
  ) where

import Control.Monad.IO.Class ( MonadIO(liftIO) ) 
import Control.Monad.State ( gets )
import Data.Text (Text)
import Data.Text qualified as T
import System.Console.Repline ( fileCompleter )

import Syntax.Common
import Parser.Parser ( programP )
import Pretty.Errors (printLocatedError)
import Repl.Repl
    ( Option(..),
      Repl,
      ReplState(replDriverState),
      prettyRepl,
      prettyText,
      parseFile )
import Driver.Driver
import Utils (trim)

-- Load

loadCmd :: Text -> Repl ()
loadCmd s = do
  let s' = T.unpack . trim $  s
  loadFile s'

loadFile :: FilePath -> Repl ()
loadFile fp = do
  decls <- parseFile fp programP
  ds <- gets replDriverState
  res <- liftIO $ inferProgramIO ds (MkModuleName "<Interactive>") decls
  case res of
    Left err -> printLocatedError err
    Right (_newEnv,_) -> do
      --modifyEnvironment (MkModuleName "FOO") undefined --(const newEnv)
      --prettyRepl newEnv
      prettyRepl $ "Successfully loaded: " ++ fp

loadOption :: Option
loadOption = Option
  { option_name = "load"
  , option_cmd = loadCmd
  , option_help = ["Load the given file from disk and add it to the environment."]
  , option_completer = Just fileCompleter
  }

-- Reload

reloadCmd :: Text -> Repl ()
reloadCmd "" = do
  prettyText ":reload currently not implemented"
reloadCmd _ = prettyText ":reload does not accept arguments"

reloadOption :: Option
reloadOption = Option
  { option_name = "reload"
  , option_cmd = reloadCmd
  , option_help = ["Reload all loaded files from disk."]
  , option_completer = Nothing
  }