module TestUtils where

import qualified Data.Map as M
import System.Directory (listDirectory)

import Parser.Parser
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

filterEnvironment :: [String] -> Environment -> Environment
filterEnvironment failingExamples Environment {..} =
  Environment { prdEnv = M.filterWithKey (\k _ -> not (k `elem` failingExamples)) prdEnv
              , cnsEnv = M.filterWithKey (\k _ -> not (k `elem` failingExamples)) cnsEnv
              , cmdEnv = cmdEnv
              , defEnv = defEnv
              , declEnv = declEnv
              }

getParsedDeclarations :: FilePath -> IO (Either Error [Declaration ()])
getParsedDeclarations fp = do
  s <- readFile fp
  return (runFileParser fp programP s)

getEnvironment :: FilePath -> [String] -> IO (Either Error Environment)
getEnvironment fp failingExamples = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> case inferProgram decls of
      Right env -> return $ Right (filterEnvironment failingExamples env)
      Left (Located _ err) -> return $ Left err
    Left err -> return $ Left err
