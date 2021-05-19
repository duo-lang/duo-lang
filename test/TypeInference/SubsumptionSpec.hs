module TypeInference.SubsumptionSpec ( spec ) where


import Test.Hspec

import TypeAutomata.Subsume (subsume)
import Parser.Parser
import Pretty.Pretty (ppPrint)
import Pretty.Types ()
import Syntax.Types

subsumptionCheck :: TypeScheme pol -> TypeScheme pol -> Spec
subsumptionCheck ts1 ts2 = do
  it (ppPrint ts1 <> " should be subsumed by " <> ppPrint ts2) $ do
    let Right b = subsume ts1 ts2
    b `shouldBe` True

subsumptionCheckPos :: String -> String -> Spec
subsumptionCheckPos s1 s2 = do
  let Right ty1 = runInteractiveParser typeSchemeP s1
  let Right ty2 = runInteractiveParser typeSchemeP s2
  subsumptionCheck ty1 ty2


spec :: Spec
spec = do
  describe "Subsumption between typeschemes works" $ do
    subsumptionCheckPos "forall a. { 'Ap(a)[a] }" "{ 'Ap(< 'True >)[< 'True >] }"
