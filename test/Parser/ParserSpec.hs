module Parser.ParserSpec ( spec ) where

import Test.Hspec
import Data.Either (isLeft)
import Data.Text (Text)
import Data.Text qualified as T

import Parser.Parser
import Parser.Types
import Syntax.Types
import Syntax.Terms
import Syntax.CommonTerm
import Pretty.Pretty (ppPrint, ppPrintString)
import Pretty.Types ()
import Pretty.Terms ()
import Translate.Translate


typeParseExample :: Text -> Typ pol -> Spec
typeParseExample input ty = do
  it ("Parsing of " ++ T.unpack input ++ " yields " ++ ppPrintString ty) $ do
    let polRep = getPolarity ty
    let Right ty2 = runInteractiveParser (typP polRep) input
    ppPrint ty `shouldBe` ppPrint ty2

typeParseCounterEx :: Text -> PolarityRep pol -> Spec
typeParseCounterEx input PosRep = do
  it ("Input " ++ T.unpack input ++ " cannot be parsed") $ do
    let res = runInteractiveParser (typP PosRep) input
    res `shouldSatisfy` isLeft
typeParseCounterEx input NegRep = do
  it ("Input " ++ T.unpack input ++ " cannot be parsed") $ do
    let res = runInteractiveParser (typP NegRep) input
    res `shouldSatisfy` isLeft

spec :: Spec
spec = do
  describe "Check type parsing" $ do
    typeParseExample "{{ Nat :>> < > }}" $ TyData PosRep (Just $ MkTypeName "Nat") []
    typeParseExample "{ 'A() }" $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "A") []]
    typeParseExample "{ 'A[{ 'B }] }" $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "A") [CnsType $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "B") []] ]]
    typeParseExample "{{Fun :>> {} }}" $ TyCodata PosRep (Just $ MkTypeName "Fun") []
    typeParseExample "< 'X({{ Nat :>> < > }}) >" $ TyData PosRep Nothing [MkXtorSig (MkXtorName Structural "X") [ PrdType $ TyData PosRep (Just $ MkTypeName "Nat") [] ]]
    typeParseExample "{{ Nat :>> < S > }}" $ TyData PosRep (Just $ MkTypeName "Nat") [MkXtorSig (MkXtorName Nominal "S") []]
    typeParseExample "{{ Foo :>> { A[{ B }] } }}" $ TyCodata PosRep (Just $ MkTypeName "Foo")
      [MkXtorSig (MkXtorName Nominal "A") [CnsType $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName Nominal "B") []] ]]
    typeParseExample "< 'A | 'B > /\\ < 'B >"
        $ TySet NegRep [ TyData   NegRep Nothing [MkXtorSig (MkXtorName Structural "A") mempty, MkXtorSig (MkXtorName Structural "B") mempty]
                       , TyData   NegRep Nothing [MkXtorSig (MkXtorName Structural "B") mempty]]
    typeParseExample "< 'A | 'B > \\/ < 'B >"
        $ TySet PosRep [ TyData   PosRep Nothing [MkXtorSig (MkXtorName Structural "A") mempty, MkXtorSig (MkXtorName Structural "B") mempty]
                       , TyData   PosRep Nothing [MkXtorSig (MkXtorName Structural "B") mempty]]
    typeParseExample "{ 'A , 'B } /\\ { 'B }"
        $ TySet NegRep [ TyCodata NegRep Nothing [MkXtorSig (MkXtorName Structural "A") mempty, MkXtorSig (MkXtorName Structural "B") mempty]
                       , TyCodata NegRep Nothing [MkXtorSig (MkXtorName Structural "B") mempty]]
    typeParseExample "{ 'A , 'B} \\/ { 'B }"
        $ TySet PosRep [ TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "A") mempty, MkXtorSig (MkXtorName Structural "B") mempty]
                       , TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "B") mempty]]
    
    typeParseCounterEx "{{ 'Ap() }" PosRep
