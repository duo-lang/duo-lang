module Main where

import System.Directory (listDirectory)
import Test.Hspec
import Test.Hspec.Runner
import Test.Hspec.Formatters

import Eval.SubstitutionSpec qualified
import TypeInference.ExamplesSpec qualified
import TypeInference.SubsumptionSpec qualified
import ParserPrettyprinter.ParserPrettyprinterSpec qualified
import Translate.FocusingSpec qualified
import Translate.TranslateExamplesSpec qualified


getAvailableCounterExamples :: IO [FilePath]
getAvailableCounterExamples = do
  examples <- listDirectory "test/counterexamples/"
  return (("test/counterexamples/" ++) <$> examples)

getAvailableExamples :: IO [FilePath]
getAvailableExamples = do
  examples <- listDirectory "examples/"
  return (("examples/" ++) <$> filter (\s -> head s /= '.') examples)

main :: IO ()
main = do
    -- Collect the filepaths of all the available examples
    examples <- getAvailableExamples
    counterExamples <- getAvailableCounterExamples
    -- Run the testsuite
    hspecWith defaultConfig { configFormatter = Just specdoc } $ do
      describe "SubstitutionSpec" (Eval.SubstitutionSpec.spec examples)
      describe "ExampleSpec" (TypeInference.ExamplesSpec.spec (examples, counterExamples))
      describe "SubsumptionSpec" TypeInference.SubsumptionSpec.spec
      describe "ParserPrettyprinterSpec" (ParserPrettyprinter.ParserPrettyprinterSpec.spec examples)
      describe "FocusingSpec" (Translate.FocusingSpec.spec examples)
      describe "TranslateExampleSpec" (Translate.TranslateExamplesSpec.spec examples)

