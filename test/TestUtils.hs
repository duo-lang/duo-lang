module TestUtils where

import System.Directory (listDirectory)

import Parser.Parser
import Syntax.Program
import TypeInference.InferProgram (inferProgram)
import qualified Data.Map as M

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

getEnvironment :: FilePath -> [String] -> IO Environment
getEnvironment fp failingExamples = do
  s <- readFile fp
  case runEnvParser programP s of
    Right decls -> return (filterEnvironment failingExamples (inferProgram decls))
    Left _err -> error $ "Could not load file: " ++ fp
