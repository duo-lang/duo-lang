module Repl.Options.Let (letOption) where

import Control.Monad.State ( gets, MonadIO(liftIO) )
import Data.Bifunctor ( Bifunctor(first) )
import Data.Text (Text)
import Data.Text qualified as T
import Text.Megaparsec ( errorBundlePretty )

import Parser.Parser ( runInteractiveParser, declarationP )
import Repl.Repl
    ( ReplState(replEnv, typeInfOpts),
      Repl,
      prettyText,
      Option(..),
      fromRight,
      modifyEnvironment )
import Syntax.Lowering.Program
import Driver.Driver

letCmd :: Text -> Repl ()
letCmd s = do
  decl <- fromRight (first (T.pack . errorBundlePretty) (runInteractiveParser declarationP s))
  oldEnv <- gets replEnv
  opts <- gets typeInfOpts
  let ds = DriverState opts oldEnv
  newEnv <- liftIO $ execDriverM ds (lowerDecl decl >>= \x -> inferDecl x)
  case newEnv of
    Left err -> prettyText (T.pack $ show err)
    Right (_,state) -> modifyEnvironment (const (driverEnv state))

letOption :: Option
letOption = Option
  { option_name = "let"
  , option_cmd = letCmd
  , option_help = [ "Add a declaration to the current environment. E.g."
                  , "\":let prd myTrue := {- Ap(x)[y] => x >> y -};\""]
  , option_completer = Nothing
  }
