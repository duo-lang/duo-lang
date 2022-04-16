module TestUtils where

import Control.Monad.Except
import Data.Text.IO qualified as T
import Data.Text qualified as T

import Driver.Definition
import Driver.Driver
import Driver.Environment
import Errors
import Parser.Parser
import Renamer.SymbolTable
import Syntax.Common
import Syntax.CST.Program qualified as CST
import Syntax.AST.Program qualified as AST


getParsedDeclarations :: FilePath -> IO (Either Error CST.Program)
getParsedDeclarations fp = do
  s <- T.readFile fp
  case runExcept (runFileParser fp programP s) of
    Left err -> pure (Left err)
    Right prog -> pure (pure prog)

getTypecheckedDecls :: FilePath -> IO (Either Error AST.Program)
getTypecheckedDecls fp = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      fmap snd <$> inferProgramIO defaultDriverState (MkModuleName (T.pack fp)) decls
    Left err -> return (Left err)

getEnvironment :: FilePath -> IO (Either Error Environment)
getEnvironment fp = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      fmap fst <$> inferProgramIO defaultDriverState (MkModuleName (T.pack fp)) decls
    Left err -> return (Left err)

getSymbolTable :: FilePath -> IO (Either Error SymbolTable)
getSymbolTable fp = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> pure (runExcept (createSymbolTable (MkModuleName "<BOOM>") decls))
    Left err -> return (Left err)
