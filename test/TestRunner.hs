module Main where

import Control.Monad.Except (runExcept, runExceptT, forM)
import Data.List.NonEmpty (NonEmpty)
import Data.Either (isRight)
import Data.List (sort)
import System.Environment (withArgs)
import Test.Hspec
import Test.Hspec.Runner
import Test.Hspec.Formatters

import Driver.Definition (defaultDriverState, parseAndCheckModule)
import Driver.Driver (inferProgramIO)
import Errors
import Resolution.SymbolTable (SymbolTable, createSymbolTable)
import Spec.LocallyClosed qualified
import Spec.TypeInferenceExamples qualified
import Spec.Prettyprinter qualified
import Spec.Focusing qualified
import Syntax.CST.Program qualified as CST
import Syntax.CST.Names
import Syntax.TST.Program qualified as TST
import Options.Applicative
import Utils (listRecursiveDuoFiles, filePathToModuleName, moduleNameToFullPath)

data Options where
  OptEmpty  :: Options
  OptFilter :: [FilePath] -> Options

getOpts :: ParserInfo Options
getOpts = info (optsP <**> helper) mempty

optsP :: Parser Options
optsP = (OptFilter <$> filterP) <|> pure OptEmpty

filterP :: Parser [FilePath]
filterP = some (argument str (metavar "FILES..." <> help "Specify files which should be tested (instead of all in the `examples/` directory"))

getAvailableCounterExamples :: IO [(FilePath, ModuleName)]
getAvailableCounterExamples = do
  let counterExFp = "test/Counterexamples/"
  examples <- listRecursiveDuoFiles counterExFp
  pure  $ zip (repeat counterExFp) $ sort examples

excluded :: [ModuleName]
excluded = []

getAvailableExamples :: IO [(FilePath, ModuleName)]
getAvailableExamples = do
  let examplesFp  = "examples/"
  let examplesFp' = "std/"
  examples <- listRecursiveDuoFiles examplesFp
  examples' <- listRecursiveDuoFiles examplesFp'
  let examplesFiltered  = filter filterFun examples
  let examplesFiltered' = filter filterFun examples'
  return $ zip (repeat examplesFp) examplesFiltered ++ zip (repeat examplesFp') examplesFiltered'
    where
      filterFun s = s `notElem` excluded

getParsedDeclarations :: FilePath -> ModuleName -> IO (Either (NonEmpty Error) CST.Module)
getParsedDeclarations fp mn = do
  let fullFp = moduleNameToFullPath mn fp
  runExceptT (parseAndCheckModule fullFp mn fp)

getTypecheckedDecls :: FilePath -> ModuleName -> IO (Either (NonEmpty Error) TST.Module)
getTypecheckedDecls fp mn = do
  decls <- getParsedDeclarations fp mn
  case decls of
    Right decls -> do
      fmap snd <$> (fst <$> inferProgramIO defaultDriverState decls)
    Left err -> return (Left err)

getSymbolTable :: FilePath -> ModuleName -> IO (Either (NonEmpty Error) SymbolTable)
getSymbolTable fp mn = do
  decls <- getParsedDeclarations fp mn
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
      OptFilter fs -> pure $ (,) "." . filePathToModuleName <$> fs
    counterExamples <- getAvailableCounterExamples
    -- Collect the parsed declarations
    parsedExamples <- forM examples $ \example -> uncurry getParsedDeclarations example >>= \res -> pure (example, res)
    parsedCounterExamples <- forM counterExamples $ \example -> uncurry getParsedDeclarations example >>= \res -> pure (example, res)
    -- Collect the typechecked declarations
    checkedExamples <- forM examples $ \example -> uncurry getTypecheckedDecls example >>= \res -> pure (example, res)
    let checkedExamplesFiltered = filter (isRight . snd) checkedExamples
    checkedCounterExamples <- forM counterExamples $ \example -> uncurry getTypecheckedDecls example >>= \res -> pure (example, res)
    -- Create symbol tables for tests
    -- Run the testsuite
    withArgs [] $ hspecWith defaultConfig { configFormatter = Just specdoc } $ do
      describe "All examples are locally closed" (Spec.LocallyClosed.spec checkedExamples)
      describe "ExampleSpec" (Spec.TypeInferenceExamples.spec parsedCounterExamples checkedCounterExamples)
      describe "Prettyprinted work again" (Spec.Prettyprinter.spec parsedExamples checkedExamplesFiltered)
      describe "Focusing works" (Spec.Focusing.spec checkedExamplesFiltered)
