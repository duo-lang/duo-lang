module TestUtils where

import qualified Data.Text.IO as T
import System.Directory (listDirectory)

import Parser.Parser
import Syntax.CommonTerm (FreeVarName)
import Syntax.Program
import TypeInference.InferProgram (inferProgram)
import TypeInference.GenerateConstraints.Definition (InferenceMode(..))
import Utils


getAvailableCounterExamples :: IO [FilePath]
getAvailableCounterExamples = do
  examples <- listDirectory "test/counterexamples/"
  return (("test/counterexamples/" ++) <$> examples)

getAvailableExamples :: FilePath -> IO [FilePath]
getAvailableExamples fp = do
  examples <- listDirectory fp
  return ((fp ++) <$> examples)

getParsedDeclarations :: FilePath -> IO (Either Error [Declaration FreeVarName])
getParsedDeclarations fp = do
  s <- T.readFile fp
  return (runFileParser fp programP s)

getEnvironment :: FilePath -> InferenceMode -> IO (Either Error (Environment FreeVarName))
getEnvironment fp im = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> case inferProgram decls im of
      Right env -> return (Right env)
      Left (Located _ err) -> return (Left err)
    Left err -> return (Left err)
