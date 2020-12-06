module SubstitutionSpec where

import           Test.Hspec
import           Control.Monad (forM_, when)

import Data.Map (Map)
import qualified Data.Map as M

import Parser
import Syntax.Terms
import Syntax.Program
import Syntax.TypeGraph
import Utils
import Eval.Substitution (isClosed_term, termLocallyClosed, checkIfBound)
import GenerateConstraints
import SolveConstraints
import TypeAutomata.Determinize
import TypeAutomata.FlowAnalysis
import TypeAutomata.Minimize (minimize)
import TypeAutomata.ToAutomaton
import TypeAutomata.Subsume (typeAutEqual)


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

