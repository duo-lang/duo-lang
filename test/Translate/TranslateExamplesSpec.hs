module Translate.TranslateExamplesSpec ( spec ) where

import Test.Hspec
import Data.Either (isRight)
import Data.Text (Text)
import Data.Text qualified as T

import Parser.Parser
import Syntax.Terms
import Syntax.CommonTerm
import Translate.Translate (compile)


compileExample :: Text -> Text -> Spec
compileExample termA termS = do
  it (T.unpack termA ++  " compiles to: " ++ T.unpack termS) $ do
      let Right (termS',_pos) = runInteractiveParser (termP PrdRep) termS
      let Right (termA',_pos) = runInteractiveParser (termP PrdRep) termA
      removeNamesTerm (compile termA') `shouldBe` removeNamesTerm (compile termS')

isClosed :: Text -> Spec
isClosed termA = do
  it ("Compilation of " ++ T.unpack termA ++  " is a closed STerm.") $ do
      let Right (termA', _pos) = runInteractiveParser (termP PrdRep) termA
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
        isClosed "cocase { Ap(x,y) => case x of {Zero => True, Succ(x) => y}}"
        isClosed "cocase { Ap(x) => case x of {Zero => x, Succ(z1,z2) => z1}}"
        isClosed "cocase { Ap(x,y) => case x of { Zero => Add(x,y), Succ(z1) => case z1 of { Zero => z1 , Succ(z2) =>  Add(x,z2)} }}"
        isClosed "cocase { Ap(x) => case x of { Zero => case x of { Zero => True }}}"

      describe "Check results of compile function:" $ do
        -- values
        compileExample "Zero" "Zero"
        compileExample "Succ(Succ(Zero))" "Succ(Succ(Zero))"
        compileExample "True" "True"
        -- complex examples
        compileExample "cocase { Ap(x,y) => case x of {Zero => True, Succ(x) => y}}"
                       "comatch { Ap(x,y)[k] => (mu m. x >> match {Zero => True >> m, Succ(z) => y >> m}) >> k}"
        compileExample "cocase { Ap(x) => case x of {Zero => x, Succ(z1,z2) => z1}}"
                       "comatch { Ap(x)[k] => (mu m. x >> match {Zero => x >> m , Succ(z1,z2) => z1 >> m}) >> k}"
        compileExample "cocase { Ap(x,y) => case x of { Zero => Add(x,y), Succ(z1) => case z1 of { Zero => z1 , Succ(z2) =>  Add(x,z2)} }}"
                       "comatch { Ap(x,y)[k] => (mu m. x >> match {Zero => Add(x, y) >> m, Succ(z1) => (mu m.z1 >> match {Zero => z1 >> m, Succ(z2) => Add(x, z2) >> m} ) >> m }) >> k }"
        compileExample "cocase { Ap(x) => case x of { Zero => case x of { Zero => True }}}"
                       "comatch { Ap(x)[k] => (mu m1. x >> match { Zero => (mu m2. x >> match {Zero => True >> m2}) >> m1} ) >> k}"
        compileExample "True.Ap(False)" "mu k. True >> Ap(False)[k]"
        compileExample "cocase {Ap(x,y) => x.Ap2(y) }"
                       "comatch { Ap(x,y)[k] => (mu k2. x >> Ap2(y)[k2]) >> k }"
        compileExample "cocase {Ap(x,y,z) => z.Ap(x,y)}"
                       "comatch { Ap(x,y,z)[k] => (mu m.z >> Ap(x,y)[m]) >> k}"
