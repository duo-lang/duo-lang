module TypeInference.SubsumptionSpec ( spec ) where

import Data.Text (Text)
import Test.Hspec

import Driver.SymbolTable
import Parser.Parser
import Pretty.Pretty (ppPrintString)
import Pretty.Types ()
import Syntax.Lowering.Types
import Syntax.AST.Types (TypeScheme)
import Syntax.Common
import TestUtils (getSymbolTable, runLowerM)
import TypeAutomata.Subsume (subsume)
import Errors

subsumptionCheckPos :: SymbolTable -> Bool -> Text -> Text -> Spec
subsumptionCheckPos symbolTable bspec s1 s2 = do
  it (ppPrintString s1 <> " should " <> (if bspec then "" else "not ") <> "subsume " <> ppPrintString s2) $ do
    let parseResult1 = runInteractiveParser typeSchemeP s1
    let parseResult2 = runInteractiveParser typeSchemeP s2
    case (parseResult1, parseResult2) of
      (Left _err, _) -> expectationFailure "Could not parse left example"
      (_, Left _err) -> expectationFailure "Could not parse right example"
      (Right r1, Right r2) -> do
        let lowerResult1 = runLowerM symbolTable (lowerTypeScheme PosRep r1) :: Either Error (TypeScheme Pos)
        let lowerResult2 = runLowerM symbolTable (lowerTypeScheme PosRep r2) :: Either Error (TypeScheme Pos)
        case (lowerResult1, lowerResult2) of
          (Left _err, _) -> expectationFailure "Could not lower left example"
          (_, Left _err) -> expectationFailure "Could not lower right example"
          (Right r1, Right r2) -> do
            let Right b = subsume r1 r2
            b `shouldBe` bspec


spec :: Spec
spec = do
  describe "Subsumption between typeschemes works" $ do
    eenv <- runIO $ getSymbolTable "examples/Peano.ds"
    let env1 = case eenv of
                Left _ -> error "Could not load Peano.ds"
                Right env -> env
    eenv <- runIO $ getSymbolTable "examples/Bool.ds"
    let env2 = case eenv of
                Left _ -> error "Could not load Bool.ds"
                Right env -> env
    let env = env1 <> env2
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

