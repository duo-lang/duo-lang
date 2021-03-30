module Translate.TranslateExamplesSpec ( spec ) where

import Test.Hspec
import Data.Either (isRight)

import Parser.Parser
import Syntax.STerms
import Translate.Translate (compile)


compileExample :: String -> String -> Spec
compileExample termA termS = do
  it (termA ++  " compiles to: " ++ termS) $ do
      let Right termS' = runInteractiveParser (stermP PrdRep) termS
      let Right termA' = runInteractiveParser atermP termA
      compile termA' `shouldBe` termS'

isClosed :: String -> Spec
isClosed termA = do
  it ("Compilation of " ++ termA ++  " is a closed STerm.") $ do
      let Right termA' = runInteractiveParser atermP termA
      termLocallyClosed (compile termA') `shouldSatisfy` isRight

-- | Compiles ATerms to STerms.
spec :: Spec
spec = do
      describe "Check if compiled STerms are locally closed:" $ do
        -- values
        isClosed "Zero"
        isClosed "Succ(Succ(Zero))"
        isClosed "True"
        -- complex examples
        isClosed "comatch { Ap(x,y) => match x with {Zero => True, Succ(x) => y}}"
        isClosed "comatch { Ap(x) => match x with {Zero => x, Succ(z1,z2) => z1}}"
        isClosed "comatch { Ap(x,y) => match x with { Zero => Add(x,y), Succ(z1) => match z1 with { Zero => z1 , Succ(z2) =>  Add(x,z2)} }}"
        isClosed "comatch { Ap(x) => match x with { Zero => match x with { Zero => True }}}"

      describe "Check results of compile function:" $ do
        -- values
        compileExample "Zero" "Zero"
        compileExample "Succ(Succ(Zero))" "Succ(Succ(Zero))"
        compileExample "True" "True"
        -- complex examples
        compileExample "comatch { Ap(x,y) => match x with {Zero => True, Succ(x) => y}}"
                       "comatch { Ap(x,y)[k] => (mu m. x >> match {Zero => True >> m, Succ(z) => y >> m}) >> k}"
        compileExample "comatch { Ap(x) => match x with {Zero => x, Succ(z1,z2) => z1}}"
                       "comatch { Ap(x)[k] => (mu m. x >> match {Zero => x >> m , Succ(z1,z2) => z1 >> m}) >> k}"
        compileExample "comatch { Ap(x,y) => match x with { Zero => Add(x,y), Succ(z1) => match z1 with { Zero => z1 , Succ(z2) =>  Add(x,z2)} }}"
                       "comatch { Ap(x,y)[k] => (mu m. x >> match {Zero => Add(x, y) >> m, Succ(z1) => (mu m.z1 >> match {Zero => z1 >> m, Succ(z2) => Add(x, z2) >> m} ) >> m }) >> k }"
        compileExample "comatch { Ap(x) => match x with { Zero => match x with { Zero => True }}}"
                       "comatch { Ap(x)[k] => (mu m1. x >> match { Zero => (mu m2. x >> match {Zero => True >> m2}) >> m1} ) >> k}"
        compileExample "True.Ap(False)" "mu k. True >> Ap(False)[k]"
        compileExample "comatch {Ap(x,y,z) => z.Ap(x,y)}"
                       "comatch { Ap(x,y,z)[k] => (mu m.z >> Ap(x,y)[m]) >> k}"