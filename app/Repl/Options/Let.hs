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
      Option(..),
      fromRight,
      modifyEnvironment )
import TypeInference.Driver

letCmd :: Text -> Repl ()
letCmd s = do
  decl <- fromRight (first (T.pack . errorBundlePretty) (runInteractiveParser declarationP s))
  oldEnv <- gets replEnv
  opts <- gets typeInfOpts
  newEnv <- liftIO $ execDriverM (DriverState opts oldEnv) (inferDecl decl)
  case newEnv of
    Left _ -> return ()
    Right (_,state) -> modifyEnvironment (const (driverEnv state))

letOption :: Option
letOption = Option
  { option_name = "let"
  , option_cmd = letCmd
  , option_help = [ "Add a declaration to the current environment. E.g."
                  , "\":let prd myTrue := {- Ap(x)[y] => x >> y -};\""]
  , option_completer = Nothing
  }
