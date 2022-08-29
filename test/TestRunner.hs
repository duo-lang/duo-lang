module Main where

import Control.Monad.Except (runExcept, forM)
import Data.List.NonEmpty (NonEmpty)
import Data.Either (isRight)
import Data.List (sort)
import Data.Text.IO qualified as T
import System.Directory (listDirectory)
import System.Environment (withArgs)
import Test.Hspec
import Test.Hspec.Runner
import Test.Hspec.Formatters

import Driver.Definition (defaultDriverState)
import Driver.Driver (inferProgramIO)
import Errors
import Parser.Definition (runFileParser)
import Parser.Program (moduleP)
import Resolution.SymbolTable (SymbolTable, createSymbolTable)
import Spec.LocallyClosed qualified
import Spec.TypeInferenceExamples qualified
import Spec.Subsumption qualified
import Spec.Prettyprinter qualified
import Spec.Focusing qualified
import Syntax.CST.Names
import Syntax.CST.Program qualified as CST
import Syntax.TST.Program qualified as TST
import Options.Applicative

data Options where
  OptEmpty  :: Options
  OptFilter :: [FilePath] -> Options

getOpts :: ParserInfo Options
getOpts = info (optsP <**> helper) mempty

optsP :: Parser Options
optsP = (OptFilter <$> filterP) <|> pure OptEmpty

filterP :: Parser [FilePath]
filterP = some (argument str (metavar "FILES..." <> help "Specify files which should be tested (instead of all in the `examples/` directory"))

getAvailableCounterExamples :: IO [FilePath]
getAvailableCounterExamples = do
  examples <- listDirectory "test/counterexamples/"
  pure  $ sort (("test/counterexamples/" ++) <$> filter (\s -> head s /= '.') examples)

excluded :: [FilePath]
excluded = ["fix.duo"]

getAvailableExamples :: IO [FilePath]
getAvailableExamples = do
  examples <- listDirectory "examples/"
  return (("examples/" ++) <$> filter (\s -> head s /= '.' && notElem s excluded) examples)

getParsedDeclarations :: FilePath -> IO (Either (NonEmpty Error) CST.Module)
getParsedDeclarations fp = do
  s <- T.readFile fp
  case runExcept (runFileParser fp (moduleP fp) s) of
    Left err -> pure (Left err)
    Right prog -> pure (pure prog)

getTypecheckedDecls :: FilePath -> IO (Either (NonEmpty Error) TST.Module)
getTypecheckedDecls fp = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      fmap snd <$> (fst <$> inferProgramIO defaultDriverState decls)
    Left err -> return (Left err)

getSymbolTable :: FilePath -> IO (Either (NonEmpty Error) SymbolTable)
getSymbolTable fp = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> pure (runExcept (createSymbolTable decls))
    Left err -> return (Left err)


main :: IO ()
main = do
    o <- execParser getOpts
    examples <- case o of
      -- Collect the filepaths of all the available examples
      OptEmpty -> getAvailableExamples
      -- only use files specified in command line
      OptFilter fs -> pure fs
    counterExamples <- getAvailableCounterExamples
    -- Collect the parsed declarations
    parsedExamples <- forM examples $ \example -> getParsedDeclarations example >>= \res -> pure (example, res)
    parsedCounterExamples <- forM counterExamples $ \example -> getParsedDeclarations example >>= \res -> pure (example, res)
    -- Collect the typechecked declarations
    checkedExamples <- forM examples $ \example -> getTypecheckedDecls example >>= \res -> pure (example, res)
    let checkedExamplesFiltered = filter (isRight . snd) checkedExamples
    checkedCounterExamples <- forM counterExamples $ \example -> getTypecheckedDecls example >>= \res -> pure (example, res)
    -- Create symbol tables for tests
    peano_st <- getSymbolTable "lib/Data/Peano.duo"
    let peano_st' = case peano_st of
                Left _ -> error "Could not load Peano.duo"
                Right peano_st' -> peano_st'
    bool_st <- getSymbolTable "lib/Data/Bool.duo"
    let bool_st' = case bool_st of
                Left _ -> error "Could not load Bool.duo"
                Right bool_st' -> bool_st'
    fun_st <- getSymbolTable "lib/Codata/Function.duo"
    let fun_st' = case fun_st of
                Left _ -> error "Could not load Function.duo"
                Right fun_st' -> fun_st'
    let symboltables = [ (MkModuleName "Peano", peano_st')
                       , (MkModuleName "Bool", bool_st')
                       , (MkModuleName "Fun", fun_st')]
    -- Run the testsuite
    withArgs [] $ hspecWith defaultConfig { configFormatter = Just specdoc } $ do
      describe "All examples are locally closed" (Spec.LocallyClosed.spec checkedExamples)
      describe "ExampleSpec" (Spec.TypeInferenceExamples.spec parsedCounterExamples checkedCounterExamples)
      describe "Subsumption works" (Spec.Subsumption.spec symboltables)
      describe "Prettyprinted work again" (Spec.Prettyprinter.spec parsedExamples checkedExamplesFiltered)
      describe "Focusing works" (Spec.Focusing.spec checkedExamplesFiltered)
