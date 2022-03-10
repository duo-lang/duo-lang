module Parser.ParserSpec ( spec ) where

import Test.Hspec
import Data.Text (Text)
import Data.Text qualified as T


import Parser.Parser
import Parser.Types (typP)
import Pretty.Errors ()
import Pretty.Terms ()
import Pretty.Types ()
import Syntax.AST.Types
import Syntax.AST.Types qualified as AST
import Syntax.Common
import Syntax.Lowering.Types
import Driver.Definition

ds :: DriverState
ds = DriverState defaultInferenceOptions mempty

parseType :: PolarityRep pol -> Text -> AST.Typ pol -> Spec
parseType pol input expected = do
  it ("Parsing of " ++ T.unpack input ++ " works") $ do
    let parseResult = runInteractiveParser typP input
    case parseResult of
      Left _err -> expectationFailure "Could not parse example type"
      Right result -> do
        lowerResult <- execDriverM ds (lowerTyp pol result)
        case lowerResult of
          Left _err -> expectationFailure "Could not lower type"
          Right (result,_) -> case pol of -- Necessary to provide Show instance for (Typ pol)
            PosRep -> result `shouldBe` expected
            NegRep -> result `shouldBe` expected

parseTypeIdentical :: PolarityRep pol -> Text -> Text -> Spec
parseTypeIdentical pol input1 input2 =
  it ("Parsing of " ++ T.unpack input1 ++ " yields the same result as parsing " ++ T.unpack input2) $ do
    let parseResult1 = runInteractiveParser typP input1
    let parseResult2 = runInteractiveParser typP input2
    case (parseResult1, parseResult2) of
      (Left _err, _) -> expectationFailure "Could not parse left example"
      (_, Left _err) -> expectationFailure "Could not parse right example"
      (Right r1, Right r2) -> do
        lowerResult1 <- execDriverM ds (lowerTyp pol r1)
        lowerResult2 <- execDriverM ds (lowerTyp pol r2)
        case (lowerResult1, lowerResult2) of
          (Left _err, _) -> expectationFailure "Could not lower left example"
          (_, Left _err) -> expectationFailure "Could not lower right example"
          (Right (r1,_), Right (r2,_)) -> case pol of -- Necessary to provide Show instance for (Typ pol)
            PosRep -> r1 `shouldBe` r2
            NegRep -> r1 `shouldBe` r2

parseTypeSchemeIdentical :: PolarityRep pol -> Text -> Text -> Spec
parseTypeSchemeIdentical pol input1 input2 = do
  it ("Parsing of " ++ T.unpack input1 ++ " yields the same result as parsing " ++ T.unpack input2) $ do
    let parseResult1 = runInteractiveParser typeSchemeP input1
    let parseResult2 = runInteractiveParser typeSchemeP input2
    case (parseResult1, parseResult2) of
      (Left _err, _) -> expectationFailure "Could not parse left example"
      (_, Left _err) -> expectationFailure "Could not parse right example"
      (Right r1, Right r2) -> do
        lowerResult1 <- execDriverM ds (lowerTypeScheme pol r1)
        lowerResult2 <- execDriverM ds (lowerTypeScheme pol r2)
        case (lowerResult1, lowerResult2) of
          (Left _err, _) -> expectationFailure "Could not lower left example"
          (_, Left _err) -> expectationFailure "Could not lower right example"
          (Right (r1,_), Right (r2,_)) -> case pol of -- Necessary to provide Show instance for (TypScheme pol)
            PosRep -> r1 `shouldBe` r2
            NegRep -> r1 `shouldBe` r2

spec :: Spec
spec = do
  describe "Check type parsing" $ do
    parseType PosRep
                 "< Nat | >"
                 (TyData PosRep (Just $ MkTypeName "Nat") [])
    parseType PosRep
                 "{ A() }"
                 (TyCodata PosRep Nothing [MkXtorSig (MkXtorName "A") []])
    parseType PosRep
                 "{ A[{ B }] }"
                 (TyCodata PosRep Nothing [MkXtorSig (MkXtorName "A") [PrdCnsType CnsRep $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName "B") []] ]])
    parseType PosRep
                 "{ Fun | }"
                 (TyCodata PosRep (Just $ MkTypeName "Fun") [])
    parseType PosRep
                 "< X(< Nat | >) >"
                 (TyData PosRep Nothing [MkXtorSig (MkXtorName "X") [ PrdCnsType PrdRep $ TyData PosRep (Just $ MkTypeName "Nat") [] ]])
    parseType PosRep
                 "< Nat | S >"
                 (TyData PosRep (Just $ MkTypeName "Nat") [MkXtorSig (MkXtorName "S") []])
    parseType PosRep
                 "{ Foo |  A[{ B }]  }"
                 (TyCodata PosRep (Just $ MkTypeName "Foo")
                           [MkXtorSig (MkXtorName "A") [PrdCnsType CnsRep $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName "B") []] ]])
    parseType NegRep
                 "< A , B > /\\ < B >"
                 (TySet NegRep Nothing [ TyData   NegRep Nothing [MkXtorSig (MkXtorName "A") mempty, MkXtorSig (MkXtorName "B") mempty]
                                       , TyData   NegRep Nothing [MkXtorSig (MkXtorName "B") mempty]])
    parseType PosRep
                 "< A , B > \\/ < B >"
                 (TySet PosRep Nothing [ TyData   PosRep Nothing [MkXtorSig (MkXtorName "A") mempty, MkXtorSig (MkXtorName "B") mempty]
                                       , TyData   PosRep Nothing [MkXtorSig (MkXtorName "B") mempty]])
    parseType NegRep
                 "{ A , B } /\\ { B }"
                 (TySet NegRep Nothing [ TyCodata NegRep Nothing [MkXtorSig (MkXtorName "A") mempty, MkXtorSig (MkXtorName "B") mempty]
                                       , TyCodata NegRep Nothing [MkXtorSig (MkXtorName "B") mempty]])
    parseType PosRep
                 "{ A , B} \\/ { B }"
                 (TySet PosRep Nothing [ TyCodata PosRep Nothing [MkXtorSig (MkXtorName "A") mempty, MkXtorSig (MkXtorName "B") mempty]
                                       , TyCodata PosRep Nothing [MkXtorSig (MkXtorName "B") mempty]])
    parseType PosRep
                 "Nat -> Nat"
                 (TyCodata PosRep Nothing [ MkXtorSig (MkXtorName "Ap")
                    [PrdCnsType PrdRep (TyNominal NegRep Nothing (MkTypeName "Nat") [] []), PrdCnsType CnsRep (TyNominal PosRep Nothing (MkTypeName "Nat") [] [])] ])
    parseType NegRep
                 "Nat -> Nat"
                 (TyCodata NegRep Nothing [ MkXtorSig (MkXtorName "Ap")
                    [PrdCnsType PrdRep (TyNominal PosRep Nothing (MkTypeName "Nat") [] []), PrdCnsType CnsRep (TyNominal NegRep Nothing (MkTypeName "Nat") [] [])] ])
    parseType PosRep
                 "Nat -> Nat -> Nat"
                 (TyCodata PosRep Nothing [ MkXtorSig (MkXtorName "Ap")
                    [PrdCnsType PrdRep (TyNominal NegRep Nothing (MkTypeName "Nat") [] []), PrdCnsType CnsRep (TyCodata PosRep Nothing [ MkXtorSig (MkXtorName "Ap")
                    [PrdCnsType PrdRep (TyNominal NegRep Nothing (MkTypeName "Nat") [] []), PrdCnsType CnsRep (TyNominal PosRep Nothing (MkTypeName "Nat") [] [])] ])] ])
    parseType NegRep
                 "Nat -> Nat -> Nat"
                 (TyCodata NegRep Nothing [ MkXtorSig (MkXtorName "Ap")
                    [PrdCnsType PrdRep (TyNominal PosRep Nothing (MkTypeName "Nat") [] []), PrdCnsType CnsRep (TyCodata NegRep Nothing [ MkXtorSig (MkXtorName "Ap")
                    [PrdCnsType PrdRep (TyNominal PosRep Nothing (MkTypeName "Nat") [] []), PrdCnsType CnsRep (TyNominal NegRep Nothing (MkTypeName "Nat") [] [])] ])] ])

    parseTypeIdentical PosRep "Nat -> Nat -> Nat" "Nat -> (Nat -> Nat)"
    parseTypeIdentical NegRep "Nat -> Nat -> Nat" "Nat -> (Nat -> Nat)"

    parseTypeSchemeIdentical PosRep "forall a b c d e f. a /\\ b -> c /\\ d -> e \\/ f" "forall a b c d e f. (a /\\ b) -> ((c /\\ d) -> (e \\/ f))"
    parseTypeSchemeIdentical NegRep "forall a b c d e f. a \\/ b -> c \\/ d -> e /\\ f" "forall a b c d e f. (a \\/ b) -> ((c \\/ d) -> (e /\\ f))"
    parseTypeSchemeIdentical PosRep "forall a b c. a \\/ b \\/ c" "forall a b c. (a \\/ b) \\/ c"
    parseTypeSchemeIdentical NegRep "forall a b c. a /\\ b /\\ c" "forall a b c. (a /\\ b) /\\ c"
