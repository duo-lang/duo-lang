module Repl.Options.Show
  ( showOption
  , showTypeOption
  ) where

import Control.Monad.State ( forM_, gets )
import Data.List (find)
import qualified Data.Map as M
import Data.Text (Text)
import System.Console.Repline ()

import Errors ()
import Parser.Parser ( programP )
import Pretty.Pretty ( NamedRep(NamedRep) )
import Pretty.Program ()
import Repl.Repl
    ( prettyText,
      prettyRepl,
      parseFile,
      Option(..),
      ReplState(loadedFiles, replEnv),
      Repl )
import Syntax.Program
    ( Environment(prdEnv, cnsEnv, cmdEnv, defEnv, declEnv) )
import Syntax.Types ( TypeName(MkTypeName), DataDecl(data_name) )
import Utils (trim)
-- Show

showCmd :: Text -> Repl ()
showCmd "" = do
  loadedFiles <- gets loadedFiles
  forM_ loadedFiles $ \fp -> do
    decls <- parseFile fp programP
    prettyRepl decls
showCmd str = do
  let s = trim str
  env <- gets replEnv
  case M.lookup s (prdEnv env) of
    Just (prd,_) -> prettyRepl (NamedRep prd)
    Nothing -> case M.lookup s (cnsEnv env) of
      Just (cns,_) -> prettyRepl (NamedRep cns)
      Nothing -> case M.lookup s (cmdEnv env) of
        Just cmd -> prettyRepl (NamedRep cmd)
        Nothing -> case M.lookup s (defEnv env) of
          Just (def,_) -> prettyRepl (NamedRep def)
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
  env <- gets (declEnv . replEnv)
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