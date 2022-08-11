module Repl.Options.Show
  ( showOption
  , showTypeOption
  ) where

import Control.Monad.State ( gets )
import Data.List (find)
import Data.Map qualified as M
import Data.Text (Text)
import System.Console.Repline ()

import Pretty.Program ()
import Repl.Repl
    ( prettyText,
      prettyRepl,
      Option(..),
      ReplState(replDriverState),
      Repl )
import Driver.Definition (DriverState(..))
import Driver.Environment
    ( Environment(prdEnv, cnsEnv, cmdEnv, declEnv))
import Syntax.Common.Names
import Syntax.RST.Program qualified as RST
import Utils (trim)


-- Show

showCmd :: Text -> Repl ()
showCmd "" = prettyText ":show needs an argument"
showCmd str = do
  let s = MkFreeVarName (trim str)
  env <- gets (M.elems . (drvEnv . replDriverState))
  let concatPrdEnv = M.unions (prdEnv  <$> env)
  let concatCnsEnv = M.unions (cnsEnv <$> env)
  let concatCmdEnv = M.unions (cmdEnv <$> env)
  case M.lookup s concatPrdEnv of
    Just (prd,_,_) -> prettyRepl prd
    Nothing -> case M.lookup s concatCnsEnv of
      Just (cns,_,_) -> prettyRepl cns
      Nothing -> case M.lookup s concatCmdEnv of
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
  env <- gets (drvEnv . replDriverState)
  let concatEnv = concat (fmap snd . declEnv <$> M.elems env)
  let maybeDecl = find (\x -> rnTnName (RST.data_name x) == MkTypeName s) concatEnv
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