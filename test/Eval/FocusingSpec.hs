module Eval.FocusingSpec ( spec ) where

import Test.Hspec
import Data.Either (isRight)

import Parser.Parser
import Syntax.STerms
import Eval.STerms (eval)



evalFocusing :: String -> String -> Spec
evalFocusing termS1 termS2 = do
  it (termA ++  " compiles to: " ++ termS) $ do
      let Right (termS1',_pos) = runInteractiveParser (stermP PrdRep) termS1
      let Right (termS2',_pos) = runInteractiveParser (stermP PrdRep) termS2
      eval (bimap (const ()) (const ()) termS1') `shouldBe` (bimap (const ()) (const ()) termS2')


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
        compileExample "comatch {Ap(x,y) => x.Ap2(y) }"
                       "comatch { Ap(x,y)[k] => (mu k2. x >> Ap2(y)[k2]) >> k }"
        compileExample "comatch {Ap(x,y,z) => z.Ap(x,y)}"
                       "comatch { Ap(x,y,z)[k] => (mu m.z >> Ap(x,y)[m]) >> k}"



-- | Compiles ATerms to STerms.
spec :: Spec
spec = do
      describe "Check if commands evaluate as expected with CBV:" $ do
        -- most of the evaluations below only evaluate to a proper value through focusing
		-- first easy example
        evalFocusing "succ >> 'Ap('S(mu k. 1 >> k))[print]"
                     "Print(3)"
        -- top level CBV focusing at match
        evalFocusing "'S(mu k. 1 >> k) >> match {'S(y) => 'S('S(y)) >> print }"
                     "Print(3)"
        -- recursive and repeated CBV focusing at match
        evalFocusing "add >> 'Ap('S(mu k.2 >> k), 'S('S(mu k. 1 >> k)))[print]"
		             "Print(6)"
        evalFocusing "mu m.(S(S(mu k.comatch{Ap(x)[n] =>  x >> match {S(y) => y >> n, Z => Z >> n}} >> Ap(Z)[k] )) >> match {Z => True >> m, S(y) => False >> m }) >> print"
                     "Print(False)"
        -- top-level CBV focusing at match and comatch
        evalFocusing "mu m.(S(mu k.comatch{Ap(x)[n] =>  x >> match {S(y) => y >> n, Z => Z >> n}} >> Ap(mu k.comatch{Ap(x)[n] => x >> n} >> Ap(Z)[k])[k] ) >> match {Z => True >> m, S(y) => False >> m }) >> print"
                     "Print(False)"
        -- recursive CBV focusing at match and comatch
        evalFocusing "mu m.(S(S(mu k.comatch{Ap(x)[n] =>  x >> match {S(y) => y >> n, Z => Z >> n}} >> Ap(S(mu k.comatch{Ap(x)[n] => x >> n} >> Ap(Z)[k]))[k] )) >> match {Z => True >> m, S(y) => False >> m }) >> print"
                     "Print(False)"
        evalFocusing "comatch {Ap(x)[k] => x >> k} >> Ap(S(S(Z)))[mu* x.x >> match{Z => True >> print, S(y) => False >> print}]"
                     "Print(False)"
        evalFocusing ""
                     ""

{-      describe "Check if commands evaluate as expected with CBV:" $ do
	    -- top-level CBN focusing at match
        evalFocusing "Ap(2)[mu* x. add >> 'Ap(x, x)[print]]  >> match{Ap(x)[k] => x >> k}"
                     "..."


comatch {Ap(x)[k] => Print(42)} >> Ap(2)[mu* x. add >> 'Ap(x)[print]]
--> error

-}