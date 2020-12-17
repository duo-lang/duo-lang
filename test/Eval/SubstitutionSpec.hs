module Eval.SubstitutionSpec where

import Test.Hspec
import qualified Data.Map as M
import Control.Monad (forM_, when)

import Syntax.Terms
import Syntax.Program
import Utils
import TestUtils
import Eval.TermSubstitution

failingExamples :: [String]
failingExamples = []

spec :: Spec
spec = do
  describe "All examples are closed" $ do
    env <- runIO $ getEnvironment "prg.txt" failingExamples
    when (failingExamples /= []) $ it "Some examples were ignored:" $ pendingWith $ unwords failingExamples
    forM_ (M.toList (prdEnv env)) $ \(name,term) -> do
      it (name ++ " does not contain free variables") $ isClosed_term term `shouldBe` True
  describe "All examples are locally closed" $ do
    env <- runIO $ getEnvironment "prg.txt" failingExamples
    when (failingExamples /= []) $ it "Some examples were ignored:" $ pendingWith $ unwords failingExamples
    forM_ (M.toList (prdEnv env)) $ \(name,term) -> do
      it (name ++ " does not contain dangling deBruijn indizes") $ termLocallyClosed term `shouldBe` True
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

