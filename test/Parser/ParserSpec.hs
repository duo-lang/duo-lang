module Parser.ParserSpec ( spec ) where

import Test.Hspec
import Data.Either (isLeft)

import Parser.Parser
import Parser.Types
import Syntax.Types
import Syntax.CommonTerm
import Pretty.Pretty (ppPrint)
import Pretty.Types ()

instance Show (Typ pol) where
  show typ = ppPrint typ

parseExample :: String -> Typ pol -> Spec
parseExample input ty = do
  it ("Parsing of " ++ input ++ " yields " ++ ppPrint ty) $ do
    let polRep = getPolarity ty
    let Right ty2 = runInteractiveParser (typP polRep) input
    ppPrint ty `shouldBe` ppPrint ty2

parseCounterEx :: String -> Typ pol -> Spec
parseCounterEx input ty = do
  it ("Input " ++ input ++ " cannot be parsed") $ do
    let polRep = getPolarity ty
    let res = runInteractiveParser (typP polRep) input
    res `shouldSatisfy` isLeft

spec :: Spec
spec = do
  describe "Check type parsing" $ do
    parseExample "{{ < > <<: Nat }}" $ TyRefined PosRep (MkTypeName "Nat") (TyData PosRep [])
    parseExample "{ 'Ap() }" $ TyCodata PosRep [MkXtorSig (MkXtorName Structural "Ap")  $ MkTypArgs [] []]
    parseExample "{{ {}<<: Fun}}" $ TyRefined PosRep (MkTypeName "Fun") (TyCodata PosRep [])
    parseCounterEx "{{ 'Ap() }" $ TyCodata PosRep [MkXtorSig (MkXtorName Structural "Ap")  $ MkTypArgs [] []]