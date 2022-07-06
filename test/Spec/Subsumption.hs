module Spec.Subsumption ( spec ) where

import Data.Text (Text)
import Data.Map qualified as M
import Test.Hspec

import Parser.Parser
import Pretty.Pretty (ppPrintString)
import Pretty.Types ()
import Resolution.Definition
import Resolution.SymbolTable
import Resolution.Types
import Syntax.Common
import TypeAutomata.Subsume (subsume)

subsumptionCheckPos :: [(ModuleName, SymbolTable)] -> Bool -> Text -> Text -> Spec
subsumptionCheckPos env bspec s1 s2 = do
  it (ppPrintString s1 <> " should " <> (if bspec then "" else "not ") <> "subsume " <> ppPrintString s2) $ do
    let parseResult1 = runInteractiveParser typeSchemeP s1
    let parseResult2 = runInteractiveParser typeSchemeP s2
    case (parseResult1, parseResult2) of
      (Left _err, _) -> expectationFailure "Could not parse left example"
      (_, Left _err) -> expectationFailure "Could not parse right example"
      (Right r1, Right r2) -> do
        let lowerResult1 = runResolverM (M.fromList env) (resolveTypeScheme PosRep r1)
        let lowerResult2 = runResolverM (M.fromList env) (resolveTypeScheme PosRep r2)
        case (lowerResult1, lowerResult2) of
          (Left _err, _) -> expectationFailure "Could not lower left example"
          (_, Left _err) -> expectationFailure "Could not lower right example"
          (Right r1, Right r2) -> do
            let Right b = subsume PosRep r1 r2
            b `shouldBe` bspec


spec :: [(ModuleName, SymbolTable)] -> Spec
spec symboltables = do
  describe "Subsumption between typeschemes works" $ do
    -- Subsumptions which should hold
    subsumptionCheckPos symboltables True "forall a. { Ap(a,return a) }" "{ Ap(< True >,return < True >) }"
    subsumptionCheckPos symboltables True "{ Ap(< True >,return < True >) }" "{ Ap(< True >,return < True >) }"
    subsumptionCheckPos symboltables True "forall a. { Ap(< True >,return < True >) }" "{ Ap(< True >,return < True >) }"
    subsumptionCheckPos symboltables True "{ Ap(< True >,return < True >) }" "forall a. { Ap(< True >,return < True >) }"
    subsumptionCheckPos symboltables True "{ Ap(< True , False >,return < True >) }" "{ Ap(< True >,return < True , False >) }"
    subsumptionCheckPos symboltables True "{ Ap( Nat , return { Ap( Nat , return Bool ) } ) }" "{ Ap( Nat , return { Ap( Nat , return Bool ) } ) }"
    subsumptionCheckPos symboltables True "Nat" "Nat"
    subsumptionCheckPos symboltables True "{ Ap(Nat,return Bool) }" "{ Ap(Nat,return Bool) }"
    subsumptionCheckPos symboltables True "rec a.  <Z, S(< S(a) >)>" "rec a. <Z, S(a)>"
    -- Subsumptions which shouldn't hold
    subsumptionCheckPos symboltables False "{}" "<>"
    subsumptionCheckPos symboltables False "{ Ap(< True >,return < True >) }" "forall a. { Ap(a,return a) }"
    subsumptionCheckPos symboltables False "{ Ap(< True >,return < True , False >) }" "{ Ap(< True >,return < True >) }"
    subsumptionCheckPos symboltables False "Nat" "Bool"

