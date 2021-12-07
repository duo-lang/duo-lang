module Parser.ParserSpec ( spec ) where

import Test.Hspec
import Data.Text (Text)
import Data.Text qualified as T

import Parser.Parser
import Parser.Types
import Pretty.Errors ()
import Pretty.Terms ()
import Pretty.Types ()
import Syntax.Types
import Syntax.CommonTerm


parseExample :: (Show a, Eq a) => Parser a -> Text -> a -> Spec
parseExample parser input expected = do
  it ("Parsing of " ++ T.unpack input ++ " works") $ do
    let parseResult = runInteractiveParser parser input
    case parseResult of
      Left _err -> expectationFailure "Could not parse example"
      Right result -> result `shouldBe` expected

parseIdentical :: (Show a, Eq a) => Parser a -> Text -> Text -> Spec
parseIdentical parser input1 input2 = do
  it ("Parsing of " ++ T.unpack input1 ++ " yields the same result as parsing " ++ T.unpack input2) $ do
    let result1 = runInteractiveParser parser input1
    let result2 = runInteractiveParser parser input2
    case (result1, result2) of
      (Left err, _) -> expectationFailure "Could not parse left example"
      (_, Left err) -> expectationFailure "Could not parse right example"
      (Right r1, Right r2) -> r1 `shouldBe` r2

spec :: Spec
spec = do
  describe "Check type parsing" $ do
    parseExample (typP PosRep)
                 "{{ Nat :>> < > }}"
                 (TyData PosRep (Just $ MkTypeName "Nat") [])
    parseExample (typP PosRep)
                 "{ 'A() }"
                 (TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "A") []])
    parseExample (typP PosRep)
                 "{ 'A[{ 'B }] }"
                 (TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "A") [CnsType $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "B") []] ]])
    parseExample (typP PosRep)
                 "{{Fun :>> {} }}"
                 (TyCodata PosRep (Just $ MkTypeName "Fun") [])
    parseExample (typP PosRep)
                 "< 'X({{ Nat :>> < > }}) >"
                 (TyData PosRep Nothing [MkXtorSig (MkXtorName Structural "X") [ PrdType $ TyData PosRep (Just $ MkTypeName "Nat") [] ]])
    parseExample (typP PosRep)
                 "{{ Nat :>> < S > }}"
                 (TyData PosRep (Just $ MkTypeName "Nat") [MkXtorSig (MkXtorName Nominal "S") []])
    parseExample (typP PosRep)
                 "{{ Foo :>> { A[{ B }] } }}"
                 (TyCodata PosRep (Just $ MkTypeName "Foo")
                           [MkXtorSig (MkXtorName Nominal "A") [CnsType $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName Nominal "B") []] ]])
    parseExample (typP NegRep)
                 "< 'A | 'B > /\\ < 'B >"
                 (TySet NegRep Nothing [ TyData   NegRep Nothing [MkXtorSig (MkXtorName Structural "A") mempty, MkXtorSig (MkXtorName Structural "B") mempty]
                                       , TyData   NegRep Nothing [MkXtorSig (MkXtorName Structural "B") mempty]])
    parseExample (typP PosRep)
                 "< 'A | 'B > \\/ < 'B >"
                 (TySet PosRep Nothing [ TyData   PosRep Nothing [MkXtorSig (MkXtorName Structural "A") mempty, MkXtorSig (MkXtorName Structural "B") mempty]
                                       , TyData   PosRep Nothing [MkXtorSig (MkXtorName Structural "B") mempty]])
    parseExample (typP NegRep)
                 "{ 'A , 'B } /\\ { 'B }"
                 (TySet NegRep Nothing [ TyCodata NegRep Nothing [MkXtorSig (MkXtorName Structural "A") mempty, MkXtorSig (MkXtorName Structural "B") mempty]
                                       , TyCodata NegRep Nothing [MkXtorSig (MkXtorName Structural "B") mempty]])
    parseExample (typP PosRep)
                 "{ 'A , 'B} \\/ { 'B }"
                 (TySet PosRep Nothing [ TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "A") mempty, MkXtorSig (MkXtorName Structural "B") mempty]
                                       , TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "B") mempty]])
    parseExample (typP PosRep)
                 "Nat -> Nat"
                 (TyCodata PosRep Nothing [ MkXtorSig (MkXtorName Structural "Ap")
                    [PrdType (TyNominal NegRep Nothing $ MkTypeName "Nat"), CnsType (TyNominal PosRep Nothing $ MkTypeName "Nat")] ])
    parseExample (typP NegRep)
                 "Nat -> Nat"
                 (TyCodata NegRep Nothing [ MkXtorSig (MkXtorName Structural "Ap")
                    [PrdType (TyNominal PosRep Nothing $ MkTypeName "Nat"), CnsType (TyNominal NegRep Nothing $ MkTypeName "Nat")] ])
    parseExample (typP PosRep)
                 "Nat -> Nat -> Nat"
                 (TyCodata PosRep Nothing [ MkXtorSig (MkXtorName Structural "Ap")
                    [PrdType (TyNominal NegRep Nothing $ MkTypeName "Nat"), CnsType (TyCodata PosRep Nothing [ MkXtorSig (MkXtorName Structural "Ap")
                    [PrdType (TyNominal NegRep Nothing $ MkTypeName "Nat"), CnsType (TyNominal PosRep Nothing $ MkTypeName "Nat")] ])] ])
    parseExample (typP NegRep)
                 "Nat -> Nat -> Nat"
                 (TyCodata NegRep Nothing [ MkXtorSig (MkXtorName Structural "Ap")
                    [PrdType (TyNominal PosRep Nothing $ MkTypeName "Nat"), CnsType (TyCodata NegRep Nothing [ MkXtorSig (MkXtorName Structural "Ap")
                    [PrdType (TyNominal PosRep Nothing $ MkTypeName "Nat"), CnsType (TyNominal NegRep Nothing $ MkTypeName "Nat")] ])] ])
    parseIdentical (typP PosRep) "Nat -> Nat -> Nat" "Nat -> (Nat -> Nat)"
    parseIdentical (typP NegRep) "Nat -> Nat -> Nat" "Nat -> (Nat -> Nat)"
    parseIdentical (typeSchemeP PosRep) "forall a b c d e f. a /\\ b -> c /\\ d -> e \\/ f" "forall a b c d e f. (a /\\ b) -> ((c /\\ d) -> (e \\/ f))"
    parseIdentical (typeSchemeP NegRep) "forall a b c d e f. a \\/ b -> c \\/ d -> e /\\ f" "forall a b c d e f. (a \\/ b) -> ((c \\/ d) -> (e /\\ f))"
    parseIdentical (typeSchemeP PosRep) "forall a b c. a \\/ b \\/ c" "forall a b c. (a \\/ b) \\/ c"
    parseIdentical (typeSchemeP NegRep) "forall a b c. a /\\ b /\\ c" "forall a b c. (a /\\ b) /\\ c"
