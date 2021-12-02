module Parser.ParserSpec ( spec ) where

import Test.Hspec
import Data.Text (Text)
import Data.Text qualified as T

import Parser.Parser
import Parser.Types
import Pretty.Errors ()
import Pretty.Pretty
import Syntax.Types
import Syntax.CommonTerm
import Pretty.Types ()
import Pretty.Terms ()

parseExample :: (Show a, Eq a) => Parser a -> Text -> a -> Spec
parseExample parser input expected = do
  it ("Parsing of " ++ T.unpack input ++ " works") $ do
    let parseResult = runInteractiveParser parser input
    case parseResult of
      Left err -> expectationFailure "Could not parse example"
      Right result -> result `shouldBe` expected

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
                 (TySet NegRep [ TyData   NegRep Nothing [MkXtorSig (MkXtorName Structural "A") mempty, MkXtorSig (MkXtorName Structural "B") mempty]
                               , TyData   NegRep Nothing [MkXtorSig (MkXtorName Structural "B") mempty]])
    parseExample (typP PosRep)
                 "< 'A | 'B > \\/ < 'B >"
                 (TySet PosRep [ TyData   PosRep Nothing [MkXtorSig (MkXtorName Structural "A") mempty, MkXtorSig (MkXtorName Structural "B") mempty]
                               , TyData   PosRep Nothing [MkXtorSig (MkXtorName Structural "B") mempty]])
    parseExample (typP NegRep)
                 "{ 'A , 'B } /\\ { 'B }"
                 (TySet NegRep [ TyCodata NegRep Nothing [MkXtorSig (MkXtorName Structural "A") mempty, MkXtorSig (MkXtorName Structural "B") mempty]
                               , TyCodata NegRep Nothing [MkXtorSig (MkXtorName Structural "B") mempty]])
    parseExample (typP PosRep)
                 "{ 'A , 'B} \\/ { 'B }"
                 (TySet PosRep [ TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "A") mempty, MkXtorSig (MkXtorName Structural "B") mempty]
                               , TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "B") mempty]])
