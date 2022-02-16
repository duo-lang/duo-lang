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
  case lowerProgram [decl] of
    Left err -> prettyText (T.pack (show err))
    Right [] -> undefined
    Right [decl] -> do
      oldEnv <- gets replEnv
      opts <- gets typeInfOpts
      newEnv <- liftIO $ execDriverM (DriverState opts oldEnv) (inferDecl decl)
      case newEnv of
        Left _ -> return ()
        Right (_,state) -> modifyEnvironment (const (driverEnv state))
    Right (_:_) -> undefined

letOption :: Option
letOption = Option
  { option_name = "let"
  , option_cmd = letCmd
  , option_help = [ "Add a declaration to the current environment. E.g."
                  , "\":let prd myTrue := {- Ap(x)[y] => x >> y -};\""]
  , option_completer = Nothing
  }
