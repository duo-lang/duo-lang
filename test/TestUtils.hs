module TestUtils where

import qualified Data.Text.IO as T
import System.Directory (listDirectory)
import System.FilePath

import Parser.Parser
import Syntax.CommonTerm (FreeVarName)
import Syntax.Program
import TypeInference.InferProgram (inferProgram)
import Utils


getAvailableCounterExamples :: IO [FilePath]
getAvailableCounterExamples = do
  examples <- listDirectory "test/counterexamples/"
  return (("test/counterexamples/" ++) <$> examples)

-- filter stuff like hidden files (e.g. artifacts from editors etc)
-- dump all your exceptions here
filterExamples :: FilePath -> Bool
filterExamples fp = not (isHidden fp || wrongFt fp)
  where
    isHidden fp = case fp of 
                    [] -> False
                    (h:_) -> h == '.'
    wrongFt fp  = takeExtension fp `elem` (("." <>) <$> ["scm", "ub"])


getAvailableExamples :: IO [FilePath]
getAvailableExamples = do
  examples <- listDirectory "examples/"
  return (("examples" </>) <$> filter filterExamples examples)

getParsedDeclarations :: FilePath -> IO (Either Error [Declaration FreeVarName])
getParsedDeclarations fp = do
  s <- T.readFile fp
  return (runFileParser fp programP s)

getEnvironment :: FilePath -> IO (Either Error (Environment FreeVarName))
getEnvironment fp = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> case inferProgram decls of
      Right env -> return (Right env)
      Left (Located _ err) -> return (Left err)
    Left err -> return (Left err)
