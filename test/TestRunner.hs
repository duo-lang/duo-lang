module Main where

import Test.Hspec.Runner
import Test.Hspec.Formatters
import Spec qualified

main :: IO ()
main = hspecWith defaultConfig { configFormatter = Just specdoc } Spec.spec
