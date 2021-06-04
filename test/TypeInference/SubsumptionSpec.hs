module TypeInference.SubsumptionSpec ( spec ) where


import Test.Hspec

import TypeAutomata.Subsume (subsume)
import Parser.Parser
import Pretty.Pretty (ppPrint)
import Pretty.Types ()
import Syntax.Types

subsumptionCheck :: TypeScheme pol -> TypeScheme pol -> Bool -> Spec
subsumptionCheck ts1 ts2 bspec = do
  it (ppPrint ts1 <> " should " <> (if bspec then "" else "not ") <> "subsume " <> ppPrint ts2) $ do
    let Right b = subsume ts1 ts2
    b `shouldBe` bspec

subsumptionCheckPos :: Bool -> String -> String -> Spec
subsumptionCheckPos b s1 s2 = do
  let Right ty1 = runInteractiveParser (typeSchemeP PosRep) s1
  let Right ty2 = runInteractiveParser (typeSchemeP PosRep) s2
  subsumptionCheck ty1 ty2 b


spec :: Spec
spec = do
  describe "Subsumption between typeschemes works" $ do
    -- Subsumptions which should hold
    subsumptionCheckPos True "forall a. { 'Ap(a)[a] }" "{ 'Ap(< 'True >)[< 'True >] }"
    subsumptionCheckPos True "{ 'Ap(< 'True >)[< 'True >] }" "{ 'Ap(< 'True >)[< 'True >] }"
    subsumptionCheckPos True "forall a. { 'Ap(< 'True >)[< 'True >] }" "{ 'Ap(< 'True >)[< 'True >] }"
    subsumptionCheckPos True "{ 'Ap(< 'True >)[< 'True >] }" "forall a. { 'Ap(< 'True >)[< 'True >] }"
    subsumptionCheckPos True "{ 'Ap(< 'True | 'False >)[< 'True >] }" "{ 'Ap(< 'True >)[< 'True | 'False >] }"
    -- Subsumptions which shouldn't hold
    subsumptionCheckPos False "{}" "<>"
    subsumptionCheckPos False "{ 'Ap(< 'True >)[< 'True >] }" "forall a. { 'Ap(a)[a] }"
    subsumptionCheckPos False "{ 'Ap(< 'True >)[< 'True | 'False >] }" "{ 'Ap(< 'True >)[< 'True >] }"
    subsumptionCheckPos False "Foo" "Bar"

