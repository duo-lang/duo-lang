module TestUtils where

import Control.Monad.Except
import Data.Text.IO qualified as T
import System.Directory (listDirectory)

import Driver.Driver
import Driver.Environment
import Errors
import Parser.Parser
import Renamer.SymbolTable
import Syntax.CST.Program qualified as CST
import Syntax.AST.Program
import Syntax.Common


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
  case runExcept (runFileParser fp programP s) of
    Left err -> pure (Left err)
    Right prog -> pure (pure prog)

getRenamedDeclarations :: FilePath -> InferenceOptions -> IO (Either Error (Program Parsed))
getRenamedDeclarations fp infopts = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      renameProgramIO (DriverState infopts mempty mempty) decls
    Left err -> return (Left err)

getTypecheckedDecls :: FilePath -> InferenceOptions -> IO (Either Error (Program Inferred))
getTypecheckedDecls fp infopts = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      fmap snd <$> inferProgramIO (DriverState infopts mempty mempty) decls
    Left err -> return (Left err)

getEnvironment :: FilePath -> InferenceOptions -> IO (Either Error (Environment Inferred))
getEnvironment fp infopts = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      fmap fst <$> inferProgramIO (DriverState infopts mempty mempty) decls
    Left err -> return (Left err)

getSymbolTable :: FilePath -> IO (Either Error SymbolTable)
getSymbolTable fp = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> pure (Right (createSymbolTable decls))
    Left err -> return (Left err)
