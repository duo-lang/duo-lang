module TestUtils where

import Parser
import Syntax.Program
import qualified Data.Map as M

filterEnvironment :: [String] -> Environment -> Environment
filterEnvironment failingExamples Environment {..} =
  Environment { prdEnv = M.filterWithKey (\k _ -> not (k `elem` failingExamples)) prdEnv
              , cnsEnv = M.filterWithKey (\k _ -> not (k `elem` failingExamples)) cnsEnv
              , typEnv = typEnv
              , declEnv = declEnv
              }

getEnvironment :: FilePath -> [String] -> IO Environment
getEnvironment fp failingExamples = do
  s <- readFile fp
  case runEnvParser environmentP mempty s of
    Right env -> return (filterEnvironment failingExamples env)
    Left _err -> error $ "Could not load file: " ++ fp
