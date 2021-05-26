module Eval.FocusingInvSpec ( spec ) where

import Test.Hspec
import TestUtils
import Data.Bifunctor

import Pretty.Pretty
import Parser.Parser
import Eval.STermsFocusInv (eval)
import Eval.Eval
import Control.Monad (forM_)


evalFocusing :: EvalOrder -> String -> String -> Spec
evalFocusing evalOrder cmd cmdRes = do
  case runInteractiveParser commandP cmd of
    Left err -> it "Could not parse" $ expectationFailure (ppPrint err)
    Right (cmd',_) -> do
      let Right (cmdRes',_) = runInteractiveParser commandP cmdRes
      prgEnv <- runIO $ getEnvironment "examples/prg.ds"
      case prgEnv of
        Left err -> it "Could not load prg.ds" $ expectationFailure (ppPrint err)
        Right prgEnv -> do
          case runEval (eval $ bimap (const ()) id cmd') evalOrder prgEnv of
            Left err -> it "Could not evaluate" $ expectationFailure (ppPrint err)
            Right b -> 
              it (cmd ++  " evaluates to: " ++ cmdRes) $ do
              b `shouldBe` (bimap (const ()) id cmdRes')


cbvExamples :: [((EvalOrder,String), String)]
cbvExamples = 
    -- CBV examples
    zip
    (zip
    (iterate id CBV)
    [
    "succ >> 'Ap('S(mu k. 1 >> k))[print]"
    , "'S(mu k. 1 >> k) >> match {'S(y) => 'S('S(y)) >> print }"
    , "add >> 'Ap('S(mu k.2 >> k), 'S('S(mu k. 1 >> k)))[print]"
    , "mu m.(S(S(mu k.comatch{Ap(x)[n] =>  x >> match {S(y) => y >> n, Z => Z >> n}} >> Ap(Z)[k] )) >> match {Z => True >> m, S(y) => False >> m }) >> print"
    , "mu m.(S(mu k.comatch{Ap(x)[n] =>  x >> match {S(y) => y >> n, Z => Z >> n}} >> Ap(mu k.comatch{Ap(x)[n] => x >> n} >> Ap(Z)[k])[k] ) >> match {Z => True >> m, S(y) => False >> m }) >> print"
    , "mu m.(S(S(mu k.comatch{Ap(x)[n] =>  x >> match {S(y) => y >> n, Z => Z >> n}} >> Ap(S(mu k.comatch{Ap(x)[n] => x >> n} >> Ap(Z)[k]))[k] )) >> match {Z => True >> m, S(y) => False >> m }) >> print"
    , "comatch {Ap(x)[k] => x >> k} >> Ap(S(S(Z)))[mu x.x >> match{Z => True >> print, S(y) => False >> print}]"
    , "times2 >> 'Ap( 'S( 'S(mu x.div2 >> 'Ap(2)[x])) )[print]"
    , "id >> 'Ap(add)['Ap('S(mu k.(2 >> k)),'S('S(mu k2.(1 >> k2))))[print]]"
    -- twice times2 (S(div2 2))
    ,"twice >> 'Ap(times2)['Ap( 'S(mu x.div2 >> 'Ap(2)[x]))[print]]"
    -- fold + 0 (map times2 (reverse [1,2]))
    , "foldl >> 'Ap(add, 0, mu k.map >> 'Ap(times2, mu k2. reverse >> 'Ap('Cons(1,'Cons(2,'Nil)))[k2])[k])[print]"
    ])
    [
    "Print(3)"
    , "Print(3)"
    , "Print(6)"
    , "Print(False)"
    , "Print(False)"
    , "Print(False)" 
    , "Print(False)" 
    , "Print(6)"
    , "Print(6)"
    , "Print(8)"
    , "Print(6)"
    ]

cbnExamples :: [((EvalOrder,String), String)]
cbnExamples =
    -- CBN examples
    zip
    (zip
    (iterate id CBN)
    [
    "id >> 'Ap(1)[mu v. v >> print]"
    , "id >> 'Ap(mu k. 1 >> k)[mu v. v >> match {'S(x) => x >> print }]"
    , "id >> 'Ap(comp)['Ap(div2, times2)['Ap(1)[mu x.Print(x)]]]])"
    , "id >> 'Ap(mu k. times3 >> 'Ap(1)[k])[mu s. add >> 'Ap(s,s)[print] ]"
    , "C(2)[C(3)['Ap[mu x.Print(x)]]] >> match{C(x)[k] => x >> k}"
    ])
    [
    "Print(mu r.(comatch {'Ap(x)[k] => x >> k} >> 'Ap('S('Z))[r]))"
    , "Print('Z)"
    , "Print(mu r.(comatch {'Ap(x)[k] => x >> k}  >> 'Ap(comp)['Ap(div2,times2)['Ap('S('Z))[r]]]))"
    , "Print('S('S('S(mu r.(comatch {'Ap(x)[k] => x >> k}  >> 'Ap(mu k.(times3 >> 'Ap(1)[k]))[r])))))"
    , "Print(mu r.(C(2)[C(3)['Ap[r]]] >> match {C(x)[k] => x >> k}))"
    ]


-- evaluate using focusing steps
spec :: Spec
spec = forM_ (cbvExamples ++ cbnExamples) $ (uncurry . uncurry) evalFocusing
