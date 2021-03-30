module TestUtils where

import System.Directory (listDirectory)

import Parser.Parser
import Syntax.CommonTerm (FreeVarName)
import Syntax.Program
import TypeInference.InferProgram (inferProgram)
import Utils


getAvailableCounterExamples :: IO [FilePath]
getAvailableCounterExamples = do
  examples <- listDirectory "test/counterexamples/"
  return (("test/counterexamples/" ++) <$> examples)

getAvailableExamples :: IO [FilePath]
getAvailableExamples = do
  examples <- listDirectory "examples/"
  return (("examples/" ++) <$> examples)

getParsedDeclarations :: FilePath -> IO (Either Error [Declaration FreeVarName])
getParsedDeclarations fp = do
  s <- readFile fp
  return (runFileParser fp programP s)

getEnvironment :: FilePath -> IO (Either Error (Environment FreeVarName))
getEnvironment fp = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> case inferProgram decls of
      Right env -> return (Right env)
      Left (Located _ err) -> return (Left err)
    Left err -> return (Left err)
