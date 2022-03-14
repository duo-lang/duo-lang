module TypeInference.SubsumptionSpec ( spec ) where

import Data.Text (Text)
import Test.Hspec

import Driver.Definition
import Parser.Parser
import Pretty.Pretty (ppPrintString)
import Pretty.Types ()
import Syntax.Lowering.Types
import Syntax.Common
import Syntax.AST.Program
import TestUtils (getEnvironment)
import TypeAutomata.Subsume (subsume)

ds :: Environment Inferred -> DriverState
ds env = DriverState defaultInferenceOptions env

subsumptionCheckPos :: Environment Inferred -> Bool -> Text -> Text -> Spec
subsumptionCheckPos env bspec s1 s2 = do
  it (ppPrintString s1 <> " should " <> (if bspec then "" else "not ") <> "subsume " <> ppPrintString s2) $ do
    let parseResult1 = runInteractiveParser typeSchemeP s1
    let parseResult2 = runInteractiveParser typeSchemeP s2
    case (parseResult1, parseResult2) of
      (Left _err, _) -> expectationFailure "Could not parse left example"
      (_, Left _err) -> expectationFailure "Could not parse right example"
      (Right r1, Right r2) -> do
        lowerResult1 <- execDriverM (ds env) (lowerTypeScheme PosRep r1)
        lowerResult2 <- execDriverM (ds env) (lowerTypeScheme PosRep r2)
        case (lowerResult1, lowerResult2) of
          (Left _err, _) -> expectationFailure "Could not lower left example"
          (_, Left _err) -> expectationFailure "Could not lower right example"
          (Right (r1,_), Right (r2,_)) -> do
            let Right b = subsume r1 r2
            b `shouldBe` bspec


spec :: Spec
spec = do
  describe "Subsumption between typeschemes works" $ do
    eenv <- runIO $ getEnvironment "examples/Prelude.ds" defaultInferenceOptions
    let env = case eenv of
                Left _ -> error "Could not load Prelude.ds"
                Right env -> env
    -- Subsumptions which should hold
    subsumptionCheckPos env True "forall a. { Ap(a)[a] }" "{ Ap(< True >)[< True >] }"
    subsumptionCheckPos env True "{ Ap(< True >)[< True >] }" "{ Ap(< True >)[< True >] }"
    subsumptionCheckPos env True "forall a. { Ap(< True >)[< True >] }" "{ Ap(< True >)[< True >] }"
    subsumptionCheckPos env True "{ Ap(< True >)[< True >] }" "forall a. { Ap(< True >)[< True >] }"
    subsumptionCheckPos env True "{ Ap(< True , False >)[< True >] }" "{ Ap(< True >)[< True , False >] }"
    subsumptionCheckPos env True "{ Ap( Nat )[ { Ap( Nat )[ Bool ] } ] }" "{ Ap( Nat )[ { Ap( Nat )[ Bool ] } ] }"
    subsumptionCheckPos env True "Nat" "Nat"
    subsumptionCheckPos env True "{ Ap(Nat)[Bool] }" "{ Ap(Nat)[Bool] }"
    -- Subsumptions which shouldn't hold
    subsumptionCheckPos env False "{}" "<>"
    subsumptionCheckPos env False "{ Ap(< True >)[< True >] }" "forall a. { Ap(a)[a] }"
    subsumptionCheckPos env False "{ Ap(< True >)[< True , False >] }" "{ Ap(< True >)[< True >] }"
    subsumptionCheckPos env False "Nat" "Bool"

