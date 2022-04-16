module Main where

import System.Directory (listDirectory)
import Test.Hspec
import Test.Hspec.Runner
import Test.Hspec.Formatters

import Spec.LocallyClosed qualified
import Spec.TypeInferenceExamples qualified
import Spec.Subsumption qualified
import Spec.Prettyprinter qualified
import Spec.Focusing qualified


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
      describe "All examples are locally closed" (Spec.LocallyClosed.spec examples)
      describe "ExampleSpec" (Spec.TypeInferenceExamples.spec (examples, counterExamples))
      describe "Subsumption works" Spec.Subsumption.spec
      describe "Prettyprinted work again" (Spec.Prettyprinter.spec examples)
      describe "Focusing works" (Spec.Focusing.spec examples)

