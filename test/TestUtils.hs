module TestUtils where

import Data.Bifunctor (first)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import System.Directory (listDirectory)
import Text.Megaparsec (errorBundlePretty)

import Errors
import Parser.Parser
import Syntax.CommonTerm
import Syntax.Program
import TypeInference.Driver

getAvailableCounterExamples :: IO [FilePath]
getAvailableCounterExamples = do
  examples <- listDirectory "test/counterexamples/"
  return (("test/counterexamples/" ++) <$> examples)

getAvailableExamples :: FilePath -> IO [FilePath]
getAvailableExamples fp = do
  examples <- listDirectory fp
  return ((fp ++) <$> filter (\s -> head s /= '.') examples)

getParsedDeclarations :: FilePath -> IO (Either Error [Declaration Parsed])
getParsedDeclarations fp = do
  s <- T.readFile fp
  return (first (ParseError Nothing . T.pack . errorBundlePretty) (runFileParser fp programP s))

getEnvironment :: FilePath -> InferenceOptions -> IO (Either Error Environment)
getEnvironment fp infopts = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      fmap fst <$> inferProgramIO (DriverState infopts mempty) decls
    Left err -> return (Left err)
