module Parser.ParserSpec ( spec ) where

import Test.Hspec
import Data.Either (isLeft)
import Data.Text (Text)
import qualified Data.Text as T

import Parser.Parser
import Parser.Types
import Syntax.Types
import Syntax.CommonTerm
import Pretty.Pretty (ppPrint, ppPrintString)
import Pretty.Types ()

instance Show (Typ pol) where
  show typ = ppPrintString typ

typeParseExample :: Text -> Typ pol -> Spec
typeParseExample input ty = do
  it ("Parsing of " ++ T.unpack input ++ " yields " ++ ppPrintString ty) $ do
    let polRep = getPolarity ty
    let Right ty2 = runInteractiveParser (typP polRep) input
    ppPrint ty `shouldBe` ppPrint ty2

typeParseCounterEx :: Text -> PolarityRep pol -> Spec
typeParseCounterEx input polRep = do
  it ("Input " ++ T.unpack input ++ " cannot be parsed") $ do
    let res = runInteractiveParser (typP polRep) input
    res `shouldSatisfy` isLeft

spec :: Spec
spec = do
  describe "Check type parsing" $ do
    typeParseExample "{{ < > <<: Nat }}" $ TyRefined PosRep (MkTypeName "Nat") (TyData PosRep [])
    typeParseExample "{ 'A() }" $ TyCodata PosRep [MkXtorSig (MkXtorName Structural "A") $ MkTypArgs [] []]
    typeParseExample "{ 'A[{ 'B }] }" $ TyCodata PosRep [MkXtorSig (MkXtorName Structural "A") $ MkTypArgs [] 
      [TyCodata PosRep [MkXtorSig (MkXtorName Structural "B") $ MkTypArgs [] []] ]]
    typeParseExample "{{ {} <<: Fun}}" $ TyRefined PosRep (MkTypeName "Fun") (TyCodata PosRep [])
    typeParseExample "< 'X({{ < > <<: Nat }}) >" $ TyData PosRep [MkXtorSig (MkXtorName Structural "X") $ MkTypArgs
      [ TyRefined PosRep (MkTypeName "Nat") (TyData PosRep []) ] []]
    typeParseExample "{{ < 'A > <<: Nat }}"$ TyRefined PosRep (MkTypeName "Nat")
      (TyData PosRep [MkXtorSig (MkXtorName Structural "A") $ MkTypArgs [] []])
    typeParseExample "{{ { 'A[{ 'B }] } <<: Foo }}" $ TyRefined PosRep (MkTypeName "Foo")
      (TyCodata PosRep [MkXtorSig (MkXtorName Structural "A") $ MkTypArgs [] 
      [TyCodata PosRep [MkXtorSig (MkXtorName Structural "B") $ MkTypArgs [] []] ]])
    --
    typeParseCounterEx "{{ 'Ap() }" PosRep
