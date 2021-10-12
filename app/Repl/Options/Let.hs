module Repl.Options.Let (letOption) where

import Control.Monad.State ( gets, MonadIO(liftIO) )
import Data.Bifunctor ( Bifunctor(first) )
import Data.Text (Text)
import qualified Data.Text as T
import Text.Megaparsec ( errorBundlePretty )

import Parser.Parser ( runInteractiveParser, declarationP )
import Repl.Repl
    ( ReplState(replEnv, typeInfVerbosity, inferenceMode),
      Repl,
      Option(..),
      fromRight,
      modifyEnvironment )
import TypeInference.InferProgram (insertDecl)

-- Define

letCmd :: Text -> Repl ()
letCmd s = do
  decl <- fromRight (first (T.pack . errorBundlePretty) (runInteractiveParser declarationP s))
  oldEnv <- gets replEnv
  verbosity <- gets typeInfVerbosity
  im <- gets inferenceMode
  newEnv <- liftIO $ insertDecl verbosity im decl oldEnv
  case newEnv of
    Left _ -> return ()
    Right newEnv -> modifyEnvironment (const newEnv)

letOption :: Option
letOption = Option
  { option_name = "let"
  , option_cmd = letCmd
  , option_help = [ "Add a declaration to the current environment. E.g."
                  , "\":let prd myTrue := {- Ap(x)[y] => x >> y -};\""]
  , option_completer = Nothing
  }
