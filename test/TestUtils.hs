module TestUtils where

import Control.Monad.Reader
import Control.Monad.Except
import Data.Text.IO qualified as T
import System.Directory (listDirectory)

import Errors
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Syntax.CST.Program qualified as CST
import Syntax.AST.Program
import Syntax.Environment
import Syntax.Common
import Driver.Driver
import Driver.SymbolTable (SymbolTable, createSymbolTable)

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
  res <- execDriverM (DriverState infopts mempty) mempty (renameProgram fp)
  case res of
    Right ((decls,_),_) -> pure (pure decls)
    Left err -> pure (Left err)

getTypecheckedDecls :: FilePath -> InferenceOptions -> IO (Either Error (Program Inferred))
getTypecheckedDecls fp infopts = do
  res <- execDriverM (DriverState infopts mempty) mempty (inferProgram fp)
  case res of
    Right ((decls,_,_),_) -> pure (pure decls)
    Left err -> pure (Left err)

getEnvironment :: FilePath -> InferenceOptions -> IO (Either Error (Environment Inferred))
getEnvironment fp infopts = do
  res <- execDriverM (DriverState infopts mempty) mempty (inferProgram fp)
  case res of
    Right ((_,_,env),_) -> pure (pure env)
    Left err -> pure (Left err)

runLowerM ::  SymbolTable -> ReaderT SymbolTable (Except Error) a -> Either Error a
runLowerM symbolTable action = runExcept (runReaderT action symbolTable)

getSymbolTable :: FilePath -> IO (Either Error SymbolTable)
getSymbolTable fp = do
  mParsedDecls <- getParsedDeclarations fp
  case mParsedDecls of
    Left err -> pure (Left err)
    Right parsedDecls -> pure (Right (createSymbolTable  parsedDecls))
