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
import Syntax.Common.Names
import Syntax.Common.Polarity
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
        let lowerResult1 = runResolverM (ResolveReader (M.fromList env) mempty 0) (resolveTypeScheme PosRep r1)
        let lowerResult2 = runResolverM (ResolveReader (M.fromList env) mempty 0) (resolveTypeScheme PosRep r2)
        case (fst lowerResult1, fst lowerResult2) of
          (Left _err, _) -> expectationFailure "Could not lower left example"
          (_, Left _err) -> expectationFailure "Could not lower right example"
          (Right r1, Right r2) -> do
            case subsume PosRep r1 r2 of
              Right b -> b `shouldBe` bspec
              Left err -> expectationFailure (show err)
            
            


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
    subsumptionCheckPos symboltables True "{ Ap(rec a. < Z, S (a) >, return (rec a.  <Z, S(< S(a) >)>) ) }" "{ Ap(rec a.  <Z, S(< S(a) >)>, return (rec a. < Z, S (a) >) ) }"
    subsumptionCheckPos symboltables True "Nat" "Nat \\/ Nat"
    subsumptionCheckPos symboltables True "rec a. < Z, S (a) >" "rec a. < Z > \\/ < S (a) >"
    subsumptionCheckPos symboltables True "<S (<Z>) >" "< Z> \\/ < S (<Z>) >"
    subsumptionCheckPos symboltables True "forall t0. (t0 -> (rec r4.(t0 \\/ < S( r4 ) >)))"
                                          "(rec b. < Z , S( b ) > ) -> (rec c. < Z , S( c ) > ) "
    -- Subsumptions which shouldn't hold
    subsumptionCheckPos symboltables False "{}" "<>"
    subsumptionCheckPos symboltables False "{ Ap(< True >,return < True >) }" "forall a. { Ap(a,return a) }"
    subsumptionCheckPos symboltables False "{ Ap(< True >,return < True , False >) }" "{ Ap(< True >,return < True >) }"
    subsumptionCheckPos symboltables False "Nat" "Bool"
    subsumptionCheckPos symboltables False "{ Ap(rec a. < Z, S ( <S(a)> ) >, return (rec a.  <Z, S(< S(a) >)>) ) }" "{ Ap(rec a.  <Z, S(a)>, return (rec a. < Z, S (a) >) ) }"
    subsumptionCheckPos symboltables False "(rec b. < Z , S( b ) > ) -> (rec c. < Z , S( c ) > ) "
                                           "forall t0. (t0 -> (rec r4.(t0 \\/ < S( r4 ) >)))"

