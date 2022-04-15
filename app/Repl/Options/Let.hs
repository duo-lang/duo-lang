module Repl.Options.Let (letOption) where

import Control.Monad.Except (runExcept)
import Control.Monad.State ( gets, MonadIO(liftIO) )
import Data.Text (Text)
import Data.Text qualified as T

import Syntax.Common
import Driver.Definition
import Driver.Driver
import Parser.Parser ( runInteractiveParser, declarationP )
import Repl.Repl
    ( ReplState(replEnv, typeInfOpts),
      Repl,
      prettyText,
      Option(..),
      fromRight,
      modifyEnvironment )

letCmd :: Text -> Repl ()
letCmd s = do
  decl <- fromRight (runExcept (runInteractiveParser declarationP s))
  oldEnv <- gets replEnv
  opts <- gets typeInfOpts
  let ds = defaultDriverState { driverEnv = oldEnv, driverOpts = opts }
  newEnv <-liftIO (inferProgramIO ds (MkModuleName "<Interactive>") [decl])
  case newEnv of
    Left err -> prettyText (T.pack $ show err)
    Right (env,_) -> modifyEnvironment (const env)

letOption :: Option
letOption = Option
  { option_name = "let"
  , option_cmd = letCmd
  , option_help = [ "Add a declaration to the current environment. E.g."
                  , "\":let prd myTrue := {- Ap(x)[y] => x >> y -};\""]
  , option_completer = Nothing
  }
