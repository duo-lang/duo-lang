module SubstitutionSpec where

import Test.Hspec

import Syntax.Terms
import Utils
import Eval.Substitution (checkIfBound)

spec :: Spec
spec = do
  describe "checkIfBound works" $ do
    it "checkIfBound [] PrdRep (0,0) `shouldBe` False" $ do
      checkIfBound [] PrdRep (0,0) `shouldBe` False
    it "checkIfBound [Twice [] []] PrdRep (0,0) = False" $ do
      checkIfBound [Twice [] []] PrdRep (0,0) `shouldBe` False
    it "checkIfBound [Twice [()] []] PrdRep (0,0) = True" $ do
      checkIfBound [Twice [()] []] PrdRep (0,0) `shouldBe` True
    it "checkIfBound [Twice [] [()]] CnsRep (0,0) = True" $ do
      checkIfBound [Twice [] [()]] CnsRep (0,0) `shouldBe` True
    it "checkIfBound [Twice [()] []] CnsRep (0,0) = False" $ do
      checkIfBound [Twice [()] []] CnsRep (0,0) `shouldBe` False

