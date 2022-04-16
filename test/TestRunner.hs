module Main where

import Control.Monad.Except (runExcept)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import System.Directory (listDirectory)
import Test.Hspec
import Test.Hspec.Runner
import Test.Hspec.Formatters

import Driver.Definition (defaultDriverState)
import Driver.Driver (inferProgramIO)
import Driver.Environment (Environment)
import Errors
import Parser.Definition (runFileParser)
import Parser.Program (programP)
import Renamer.SymbolTable (SymbolTable, createSymbolTable)
import Spec.LocallyClosed qualified
import Spec.TypeInferenceExamples qualified
import Spec.Subsumption qualified
import Spec.Prettyprinter qualified
import Spec.Focusing qualified
import Syntax.Common
import Syntax.CST.Program qualified as CST
import Syntax.AST.Program qualified as AST


getAvailableCounterExamples :: IO [FilePath]
getAvailableCounterExamples = do
  examples <- listDirectory "test/counterexamples/"
  return (("test/counterexamples/" ++) <$> examples)

getAvailableExamples :: IO [FilePath]
getAvailableExamples = do
  examples <- listDirectory "examples/"
  return (("examples/" ++) <$> filter (\s -> head s /= '.') examples)

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


main :: IO ()
main = do
    -- Collect the filepaths of all the available examples
    examples <- getAvailableExamples
    counterExamples <- getAvailableCounterExamples
    -- Create symbol tables for tests
    peano_st <- getSymbolTable "examples/Peano.ds"
    let peano_st' = case peano_st of
                Left _ -> error "Could not load Peano.ds"
                Right peano_st' -> peano_st'
    bool_st <- getSymbolTable "examples/Bool.ds"
    let bool_st' = case bool_st of
                Left _ -> error "Could not load Bool.ds"
                Right bool_st' -> bool_st'
    let symboltables = [(MkModuleName "Peano", peano_st'), (MkModuleName "Bool", bool_st')]
    -- Run the testsuite
    hspecWith defaultConfig { configFormatter = Just specdoc } $ do
      describe "All examples are locally closed" (Spec.LocallyClosed.spec examples)
      describe "ExampleSpec" (Spec.TypeInferenceExamples.spec (examples, counterExamples))
      describe "Subsumption works" (Spec.Subsumption.spec symboltables)
      describe "Prettyprinted work again" (Spec.Prettyprinter.spec examples)
      describe "Focusing works" (Spec.Focusing.spec examples)

