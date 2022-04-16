module Main where

import Test.Hspec
import Test.Hspec.Runner
import Test.Hspec.Formatters

import Eval.SubstitutionSpec qualified
import TypeInference.ExamplesSpec qualified
import TypeInference.SubsumptionSpec qualified
import ParserPrettyprinter.ParserPrettyprinterSpec qualified
import Translate.FocusingSpec qualified
import Translate.TranslateExamplesSpec qualified

main :: IO ()
main = hspecWith defaultConfig { configFormatter = Just specdoc } spec


spec :: Spec
spec = do
    describe "SubstitutionSpec" Eval.SubstitutionSpec.spec
    describe "ExampleSpec" TypeInference.ExamplesSpec.spec
    describe "SubsumptionSpec" TypeInference.SubsumptionSpec.spec
    describe "ParserPrettyprinterSpec" ParserPrettyprinter.ParserPrettyprinterSpec.spec
    describe "FocusingSpec" Translate.FocusingSpec.spec
    describe "TranslateExampleSpec" Translate.TranslateExamplesSpec.spec

