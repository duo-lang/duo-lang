module TestUtils where

import Data.Text qualified as T
import Data.Text.IO qualified as T
import System.Directory (listDirectory)
import Text.Megaparsec (errorBundlePretty)

import Errors
import Parser.Parser
import Syntax.CST.Program qualified as CST
import Syntax.AST.Program
import Syntax.Common
import Driver.Driver

getAvailableCounterExamples :: IO [FilePath]
getAvailableCounterExamples = do
  examples <- listDirectory "test/counterexamples/"
  return (("test/counterexamples/" ++) <$> examples)

getAvailableExamples :: FilePath -> IO [FilePath]
getAvailableExamples fp = do
  examples <- listDirectory fp
  return ((fp ++) <$> filter (\s -> head s /= '.') examples)

getParsedDeclarations :: FilePath -> IO (Either Error CST.Program)
getParsedDeclarations fp = do
  s <- T.readFile fp
  case runFileParser fp programP s of
    Left err -> pure (Left (ParseError Nothing (T.pack (errorBundlePretty err))))
    Right prog -> pure (pure prog)

getRenamedDeclarations :: FilePath -> InferenceOptions -> IO (Either Error (Program Parsed))
getRenamedDeclarations fp infopts = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      renameProgramIO (DriverState infopts mempty) decls
    Left err -> return (Left err)

getTypecheckedDecls :: FilePath -> InferenceOptions -> IO (Either Error (Program Inferred))
getTypecheckedDecls fp infopts = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      fmap snd <$> inferProgramIO (DriverState infopts mempty) decls
    Left err -> return (Left err)

getEnvironment :: FilePath -> InferenceOptions -> IO (Either Error (Environment Inferred))
getEnvironment fp infopts = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      fmap fst <$> inferProgramIO (DriverState infopts mempty) decls
    Left err -> return (Left err)

