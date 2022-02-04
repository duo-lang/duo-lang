module TypeInference.SubsumptionSpec ( spec ) where

import Data.Text (Text)
import Test.Hspec
import TestUtils

import TypeAutomata.Subsume (subsume)
import Parser.Parser
import Pretty.Pretty (ppPrintString)
import Pretty.Types ()
import Syntax.AST.Types

subsumptionCheck :: TypeScheme pol -> TypeScheme pol -> Bool -> Spec
subsumptionCheck ts1 ts2 bspec = do
  it (ppPrintString ts1 <> " should " <> (if bspec then "" else "not ") <> "subsume " <> ppPrintString ts2) $ do
    let Right b = subsume ts1 ts2
    b `shouldBe` bspec

subsumptionCheckPos :: Bool -> Text -> Text -> Spec
subsumptionCheckPos b s1 s2 = do
  let Right ty1 = runInteractiveParser (typeSchemePLowering PosRep) s1
  let Right ty2 = runInteractiveParser (typeSchemePLowering PosRep) s2
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
    subsumptionCheckPos True "{ 'Ap( Nat )[ { 'Ap( Nat )[ Bool ] } ] }" "{ 'Ap( Nat )[ { 'Ap( Nat )[ Bool ] } ] }"
    subsumptionCheckPos True "Nat" "Nat"
    subsumptionCheckPos True "{ 'Ap(Nat)[Bool] }" "{ 'Ap(Nat)[Bool] }"
    -- Subsumptions which shouldn't hold
    subsumptionCheckPos False "{}" "<>"
    subsumptionCheckPos False "{ 'Ap(< 'True >)[< 'True >] }" "forall a. { 'Ap(a)[a] }"
    subsumptionCheckPos False "{ 'Ap(< 'True >)[< 'True | 'False >] }" "{ 'Ap(< 'True >)[< 'True >] }"
    subsumptionCheckPos False "Foo" "Bar"

