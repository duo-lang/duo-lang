module TypeInference.SubsumptionSpec ( spec ) where

import Data.Text (Text)
import Test.Hspec

import Driver.Definition
import Parser.Parser
import Pretty.Pretty (ppPrintString)
import Pretty.Types ()
import Syntax.AST.Types
import Syntax.Lowering.Types
import TypeAutomata.Subsume (subsume)

ds :: DriverState
ds = DriverState defaultInferenceOptions mempty

subsumptionCheckPos :: Bool -> Text -> Text -> Spec
subsumptionCheckPos bspec s1 s2 = do
  it (ppPrintString s1 <> " should " <> (if bspec then "" else "not ") <> "subsume " <> ppPrintString s2) $ do
    let parseResult1 = runInteractiveParser typeSchemeP s1
    let parseResult2 = runInteractiveParser typeSchemeP s2
    case (parseResult1, parseResult2) of
      (Left _err, _) -> expectationFailure "Could not parse left example"
      (_, Left _err) -> expectationFailure "Could not parse right example"
      (Right r1, Right r2) -> do
        lowerResult1 <- execDriverM ds (lowerTypeScheme PosRep r1)
        lowerResult2 <- execDriverM ds (lowerTypeScheme PosRep r2)
        case (lowerResult1, lowerResult2) of
          (Left _err, _) -> expectationFailure "Could not lower left example"
          (_, Left _err) -> expectationFailure "Could not lower right example"
          (Right (r1,_), Right (r2,_)) -> do
            let Right b = subsume r1 r2
            b `shouldBe` bspec


spec :: Spec
spec = do
  describe "Subsumption between typeschemes works" $ do
    -- Subsumptions which should hold
    subsumptionCheckPos True "forall a. { Ap(a)[a] }" "{ Ap(< True >)[< True >] }"
    subsumptionCheckPos True "{ Ap(< True >)[< True >] }" "{ Ap(< True >)[< True >] }"
    subsumptionCheckPos True "forall a. { Ap(< True >)[< True >] }" "{ Ap(< True >)[< True >] }"
    subsumptionCheckPos True "{ Ap(< True >)[< True >] }" "forall a. { Ap(< True >)[< True >] }"
    subsumptionCheckPos True "{ Ap(< True | False >)[< True >] }" "{ Ap(< True >)[< True | False >] }"
    subsumptionCheckPos True "{ Ap( Nat )[ { Ap( Nat )[ Bool ] } ] }" "{ Ap( Nat )[ { Ap( Nat )[ Bool ] } ] }"
    subsumptionCheckPos True "Nat" "Nat"
    subsumptionCheckPos True "{ Ap(Nat)[Bool] }" "{ Ap(Nat)[Bool] }"
    -- Subsumptions which shouldnt hold
    subsumptionCheckPos False "{}" "<>"
    subsumptionCheckPos False "{ Ap(< True >)[< True >] }" "forall a. { Ap(a)[a] }"
    subsumptionCheckPos False "{ Ap(< True >)[< True | False >] }" "{ Ap(< True >)[< True >] }"
    subsumptionCheckPos False "Foo" "Bar"

