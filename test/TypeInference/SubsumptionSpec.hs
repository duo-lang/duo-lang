module TypeInference.SubsumptionSpec ( spec ) where

import Data.Text (Text)
import Test.Hspec

import Parser.Parser
import Pretty.Pretty (ppPrintString)
import Pretty.Types ()
import Renamer.Definition
import Renamer.SymbolTable
import Renamer.Types
import Syntax.Common
import TestUtils (getSymbolTable)
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
        let lowerResult1 = runRenamerM env (renameTypeScheme PosRep r1)
        let lowerResult2 = runRenamerM env (renameTypeScheme PosRep r2)
        case (lowerResult1, lowerResult2) of
          (Left _err, _) -> expectationFailure "Could not lower left example"
          (_, Left _err) -> expectationFailure "Could not lower right example"
          (Right r1, Right r2) -> do
            let Right b = subsume PosRep r1 r2
            b `shouldBe` bspec


spec :: Spec
spec = do
  describe "Subsumption between typeschemes works" $ do
    eenv <- runIO $ getSymbolTable "examples/Peano.ds"
    let env' = case eenv of
                Left _ -> error "Could not load Peano.ds"
                Right env -> env
    eenv' <- runIO $ getSymbolTable "examples/Bool.ds"
    let env'' = case eenv' of
                Left _ -> error "Could not load Bool.ds"
                Right env -> env
    let env = [(MkModuleName "Peano", env'), (MkModuleName "Bool", env'')]
    -- Subsumptions which should hold
    subsumptionCheckPos env True "forall a. { Ap(a,return a) }" "{ Ap(< True >,return < True >) }"
    subsumptionCheckPos env True "{ Ap(< True >,return < True >) }" "{ Ap(< True >,return < True >) }"
    subsumptionCheckPos env True "forall a. { Ap(< True >,return < True >) }" "{ Ap(< True >,return < True >) }"
    subsumptionCheckPos env True "{ Ap(< True >,return < True >) }" "forall a. { Ap(< True >,return < True >) }"
    subsumptionCheckPos env True "{ Ap(< True , False >,return < True >) }" "{ Ap(< True >,return < True , False >) }"
    subsumptionCheckPos env True "{ Ap( Nat , return { Ap( Nat , return Bool ) } ) }" "{ Ap( Nat , return { Ap( Nat , return Bool ) } ) }"
    subsumptionCheckPos env True "Nat" "Nat"
    subsumptionCheckPos env True "{ Ap(Nat,return Bool) }" "{ Ap(Nat,return Bool) }"
    -- Subsumptions which shouldn't hold
    subsumptionCheckPos env False "{}" "<>"
    subsumptionCheckPos env False "{ Ap(< True >,return < True >) }" "forall a. { Ap(a,return a) }"
    subsumptionCheckPos env False "{ Ap(< True >,return < True , False >) }" "{ Ap(< True >,return < True >) }"
    subsumptionCheckPos env False "Nat" "Bool"

