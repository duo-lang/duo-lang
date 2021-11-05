module Parser.ParserSpec ( spec ) where

import Test.Hspec
import Data.Either (isLeft)
import Data.Text (Text)
import Data.Text qualified as T

import Parser.Parser
import Parser.Types
import Syntax.Types
import Syntax.ATerms
import Pretty.Pretty (ppPrint, ppPrintString)
import Pretty.Types ()
import Pretty.ATerms ()
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

atermParseExample :: Text -> ATerm Compiled -> Spec
atermParseExample input tm = do
  it ("Parsing of " ++ T.unpack input ++ " yields " ++ ppPrintString tm) $ do
    let Right (parsedTerm,_) = runInteractiveParser atermP input
    compileATerm parsedTerm `shouldBe` tm

spec :: Spec
spec = do
  describe "Check type parsing" $ do
    typeParseExample "{{ Nat :>> < > }}" $ TyData PosRep (Just $ MkTypeName "Nat") []
    typeParseExample "{ 'A() }" $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "A") $ MkTypArgs [] []]
    typeParseExample "{ 'A[{ 'B }] }" $ TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "A") $ MkTypArgs [] 
      [TyCodata PosRep Nothing [MkXtorSig (MkXtorName Structural "B") $ MkTypArgs [] []] ]]
    typeParseExample "{{Fun :>> {} }}" $ TyCodata PosRep (Just $ MkTypeName "Fun") []
    typeParseExample "< 'X({{ Nat :>> < > }}) >" $ TyData PosRep Nothing [MkXtorSig (MkXtorName Structural "X") $ MkTypArgs
      [ TyData PosRep (Just $ MkTypeName "Nat") [] ] []]
    typeParseExample "{{ Nat :>> < S > }}" $ TyData PosRep (Just $ MkTypeName "Nat")
      [MkXtorSig (MkXtorName Nominal "S") $ MkTypArgs [] []]
    typeParseExample "{{ Foo :>> { A[{ B }] } }}" $ TyCodata PosRep (Just $ MkTypeName "Foo")
      [MkXtorSig (MkXtorName Nominal "A") $ MkTypArgs [] 
      [TyCodata PosRep Nothing [MkXtorSig (MkXtorName Nominal "B") $ MkTypArgs [] []] ]]
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
    --
    typeParseCounterEx "{{ 'Ap() }" PosRep
  describe "Check aterm parsing" $ do
    atermParseExample "x y z" (Dtor () (MkXtorName Structural "Ap")
                                       (Dtor () (MkXtorName Structural "Ap") (FVar () "x") [FVar () "y"]) [FVar () "z"])
    atermParseExample "x.A.B" (Dtor () (MkXtorName Nominal "B")
                                       (Dtor () (MkXtorName Nominal "A") (FVar () "x") []) [])
    atermParseExample "f C(x)" (Dtor () (MkXtorName Structural "Ap") (FVar () "f") [Ctor () (MkXtorName Nominal "C") [FVar () "x"]])
 