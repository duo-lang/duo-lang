module Parser.ParserSpec ( spec ) where

import Test.Hspec
import Data.Text (Text)
import Data.Text qualified as T


import Parser.Parser
import Pretty.Errors ()
import Pretty.Terms ()
import Pretty.Types ()
import Syntax.AST.Types
import Syntax.CommonTerm
import TestUtils

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
      (Left _err, _) -> expectationFailure "Could not parse left example"
      (_, Left _err) -> expectationFailure "Could not parse right example"
      (Right r1, Right r2) -> r1 `shouldBe` r2

spec :: Spec
spec = do
  describe "Check type parsing" $ do
    parseExample (typPLowering PosRep)
                 "{{ Nat :>> < > }}"
                 (TyData PosRep (Just $ MkTypeName "Nat") [])
    parseExample (typPLowering PosRep)
                 "{ 'A() }"
                 (TyCodata PosRep Nothing [MkXtorSig (MkXtorName "A") []])
    parseExample (typPLowering PosRep)
                 "{ 'A[{ 'B }] }"
                 (TyCodata PosRep Nothing [MkXtorSig (MkXtorName "A") [PrdCnsType CnsRep $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName "B") []] ]])
    parseExample (typPLowering PosRep)
                 "{{Fun :>> {} }}"
                 (TyCodata PosRep (Just $ MkTypeName "Fun") [])
    parseExample (typPLowering PosRep)
                 "< 'X({{ Nat :>> < > }}) >"
                 (TyData PosRep Nothing [MkXtorSig (MkXtorName "X") [ PrdCnsType PrdRep $ TyData PosRep (Just $ MkTypeName "Nat") [] ]])
    parseExample (typPLowering PosRep)
                 "{{ Nat :>> < S > }}"
                 (TyData PosRep (Just $ MkTypeName "Nat") [MkXtorSig (MkXtorName "S") []])
    parseExample (typPLowering PosRep)
                 "{{ Foo :>> { A[{ B }] } }}"
                 (TyCodata PosRep (Just $ MkTypeName "Foo")
                           [MkXtorSig (MkXtorName "A") [PrdCnsType CnsRep $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName "B") []] ]])
    parseExample (typPLowering NegRep)
                 "< 'A | 'B > /\\ < 'B >"
                 (TySet NegRep Nothing [ TyData   NegRep Nothing [MkXtorSig (MkXtorName "A") mempty, MkXtorSig (MkXtorName "B") mempty]
                                       , TyData   NegRep Nothing [MkXtorSig (MkXtorName "B") mempty]])
    parseExample (typPLowering PosRep)
                 "< 'A | 'B > \\/ < 'B >"
                 (TySet PosRep Nothing [ TyData   PosRep Nothing [MkXtorSig (MkXtorName "A") mempty, MkXtorSig (MkXtorName "B") mempty]
                                       , TyData   PosRep Nothing [MkXtorSig (MkXtorName "B") mempty]])
    parseExample (typPLowering NegRep)
                 "{ 'A , 'B } /\\ { 'B }"
                 (TySet NegRep Nothing [ TyCodata NegRep Nothing [MkXtorSig (MkXtorName "A") mempty, MkXtorSig (MkXtorName "B") mempty]
                                       , TyCodata NegRep Nothing [MkXtorSig (MkXtorName "B") mempty]])
    parseExample (typPLowering PosRep)
                 "{ 'A , 'B} \\/ { 'B }"
                 (TySet PosRep Nothing [ TyCodata PosRep Nothing [MkXtorSig (MkXtorName "A") mempty, MkXtorSig (MkXtorName "B") mempty]
                                       , TyCodata PosRep Nothing [MkXtorSig (MkXtorName "B") mempty]])
    parseExample (typPLowering PosRep)
                 "Nat -> Nat"
                 (TyCodata PosRep Nothing [ MkXtorSig (MkXtorName "Ap")
                    [PrdCnsType PrdRep (TyNominal NegRep Nothing $ MkTypeName "Nat"), PrdCnsType CnsRep (TyNominal PosRep Nothing $ MkTypeName "Nat")] ])
    parseExample (typPLowering NegRep)
                 "Nat -> Nat"
                 (TyCodata NegRep Nothing [ MkXtorSig (MkXtorName "Ap")
                    [PrdCnsType PrdRep (TyNominal PosRep Nothing $ MkTypeName "Nat"), PrdCnsType CnsRep (TyNominal NegRep Nothing $ MkTypeName "Nat")] ])
    parseExample (typPLowering PosRep)
                 "Nat -> Nat -> Nat"
                 (TyCodata PosRep Nothing [ MkXtorSig (MkXtorName "Ap")
                    [PrdCnsType PrdRep (TyNominal NegRep Nothing $ MkTypeName "Nat"), PrdCnsType CnsRep (TyCodata PosRep Nothing [ MkXtorSig (MkXtorName "Ap")
                    [PrdCnsType PrdRep (TyNominal NegRep Nothing $ MkTypeName "Nat"), PrdCnsType CnsRep (TyNominal PosRep Nothing $ MkTypeName "Nat")] ])] ])
    parseExample (typPLowering NegRep)
                 "Nat -> Nat -> Nat"
                 (TyCodata NegRep Nothing [ MkXtorSig (MkXtorName "Ap")
                    [PrdCnsType PrdRep (TyNominal PosRep Nothing $ MkTypeName "Nat"), PrdCnsType CnsRep (TyCodata NegRep Nothing [ MkXtorSig (MkXtorName "Ap")
                    [PrdCnsType PrdRep (TyNominal PosRep Nothing $ MkTypeName "Nat"), PrdCnsType CnsRep (TyNominal NegRep Nothing $ MkTypeName "Nat")] ])] ])
    parseIdentical (typPLowering PosRep) "Nat -> Nat -> Nat" "Nat -> (Nat -> Nat)"
    parseIdentical (typPLowering NegRep) "Nat -> Nat -> Nat" "Nat -> (Nat -> Nat)"
    parseIdentical (typeSchemePLowering PosRep) "forall a b c d e f. a /\\ b -> c /\\ d -> e \\/ f" "forall a b c d e f. (a /\\ b) -> ((c /\\ d) -> (e \\/ f))"
    parseIdentical (typeSchemePLowering NegRep) "forall a b c d e f. a \\/ b -> c \\/ d -> e /\\ f" "forall a b c d e f. (a \\/ b) -> ((c \\/ d) -> (e /\\ f))"
    parseIdentical (typeSchemePLowering PosRep) "forall a b c. a \\/ b \\/ c" "forall a b c. (a \\/ b) \\/ c"
    parseIdentical (typeSchemePLowering NegRep) "forall a b c. a /\\ b /\\ c" "forall a b c. (a /\\ b) /\\ c"
