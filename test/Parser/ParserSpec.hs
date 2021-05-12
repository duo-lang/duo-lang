module Parser.ParserSpec ( spec ) where

import Test.Hspec
import Data.Bifunctor
import Data.Either (isRight)

import Parser.Parser
import Syntax.STerms


-- | Compiles ATerms to STerms.
spec :: Spec
spec = do
      describe "Check arithmetic" $ do
        it "2 + 2 equals 4" $ do
          (2 + 2) `shouldBe` 4

