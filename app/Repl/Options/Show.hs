module Repl.Options.Show
  ( showOption
  , showTypeOption
  ) where

import Control.Monad.State ( forM_, gets, MonadIO(liftIO) )
import Data.List (find)
import Data.Map qualified as M
import Data.Text (Text)
import Data.Text qualified as T
import System.Console.Repline ()

import Parser.Parser ( programP )
import Pretty.Program ()
import Repl.Repl
    ( prettyText,
      prettyRepl,
      parseFile,
      Option(..),
      ReplState(loadedFiles, replEnv, typeInfOpts),
      Repl )
import Driver.Environment
    ( Environment(prdEnv, cnsEnv, cmdEnv, declEnv) )
import Renamer.Program    
import Syntax.RST.Types ( DataDecl(data_name) )
import Syntax.Common
import Driver.Definition
import Utils (trim)

-- Show

showCmd :: Text -> Repl ()
showCmd "" = do
  loadedFiles <- gets loadedFiles
  oldEnv <- gets replEnv
  opts <- gets typeInfOpts
  let ds = DriverState opts oldEnv mempty
  forM_ loadedFiles $ \fp -> do
    decls <- parseFile fp programP
    decls' <- liftIO $ execDriverM ds $ renameProgram decls
    case decls' of
      Left err -> prettyText (T.pack $ show err)
      Right (decls,_) -> prettyRepl decls
showCmd str = do
  let s = MkFreeVarName (trim str)
  env <- gets replEnv
  case M.lookup s (prdEnv env) of
    Just (prd,_,_) -> prettyRepl prd
    Nothing -> case M.lookup s (cnsEnv env) of
      Just (cns,_,_) -> prettyRepl cns
      Nothing -> case M.lookup s (cmdEnv env) of
        Just (cmd,_) -> prettyRepl cmd
        Nothing -> prettyText "Not in environment."

showOption :: Option
showOption = Option
  { option_name = "show"
  , option_cmd = showCmd
  , option_help = ["Display term or type on the command line."]
  , option_completer = Nothing
  }

-- Show TypeDeclaration

showTypeCmd :: Text -> Repl ()
showTypeCmd s = do
  env <- gets (fmap snd . declEnv . replEnv)
  let maybeDecl = find (\x -> data_name x == MkTypeName s) env
  case maybeDecl of
    Nothing -> prettyRepl ("Type: " <> s <> " not found in environment.")
    Just decl -> prettyRepl decl

showTypeOption :: Option
showTypeOption = Option
  { option_name = "showtype"
  , option_cmd = showTypeCmd
  , option_help = ["Show the definition of a nominal type"]
  , option_completer = Nothing
  }