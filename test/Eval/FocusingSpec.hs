module Eval.FocusingSpec ( spec ) where

import Test.Hspec
import TestUtils
import Data.Bifunctor

import Pretty.Pretty
import Parser.Parser
import Eval.STerms (eval)
import Eval.Eval


evalFocusing :: EvalOrder -> String -> String -> Spec
evalFocusing evalOrder cmd cmdRes = do
  let Right (cmd',_) = runInteractiveParser commandP cmd
  let Left _ = runInteractiveParser commandP cmd
  let Right (cmdRes',_) = runInteractiveParser commandP cmdRes
  let Left _ = runInteractiveParser commandP cmdRes
  prgEnv <- runIO $ getEnvironment "examples/prg.ds"
  case prgEnv of
    Left err -> it "Could not load prg.ds" $ expectationFailure (ppPrint err)
    Right prgEnv -> do
      case runEval (eval $ bimap (const ()) id cmd') evalOrder prgEnv of
        Left err -> it "Could not load evaluate" $ expectationFailure (ppPrint err)
        Right b -> 
          it (cmd ++  " evaluates to: " ++ cmdRes) $ do
          b `shouldBe` (bimap (const ()) id cmdRes')


-- | Compiles ATerms to STerms.
spec :: Spec
spec = do
      describe "Check if commands evaluate as expected with CBV:" $ do
        -- most of the evaluations below only evaluate to a proper value through focusing
       -- first easy example
        evalFocusing CBV 
                     "succ >> 'Ap('S(mu k. 1 >> k))[print]"
                     "Print(3)"
        -- top level CBV focusing at match
        evalFocusing CBV 
                     "'S(mu k. 1 >> k) >> match {'S(y) => 'S('S(y)) >> print }"
                     "Print(3)"
        -- recursive and repeated CBV focusing at match
        evalFocusing CBV
                     "add >> 'Ap('S(mu k.2 >> k), 'S('S(mu k. 1 >> k)))[print]"
                     "Print(6)"
        evalFocusing CBV
                     "mu m.(S(S(mu k.comatch{Ap(x)[n] =>  x >> match {S(y) => y >> n, Z => Z >> n}} >> Ap(Z)[k] )) >> match {Z => True >> m, S(y) => False >> m }) >> print"
                     "Print(False)"
        -- top-level CBV focusing at match and comatch
        evalFocusing CBV
                     "mu m.(S(mu k.comatch{Ap(x)[n] =>  x >> match {S(y) => y >> n, Z => Z >> n}} >> Ap(mu k.comatch{Ap(x)[n] => x >> n} >> Ap(Z)[k])[k] ) >> match {Z => True >> m, S(y) => False >> m }) >> print"
                     "Print(False)"
        -- recursive CBV focusing at match and comatch
        evalFocusing CBV
                     "mu m.(S(S(mu k.comatch{Ap(x)[n] =>  x >> match {S(y) => y >> n, Z => Z >> n}} >> Ap(S(mu k.comatch{Ap(x)[n] => x >> n} >> Ap(Z)[k]))[k] )) >> match {Z => True >> m, S(y) => False >> m }) >> print"
                     "Print(False)"
        evalFocusing CBV
                     "comatch {Ap(x)[k] => x >> k} >> Ap(S(S(Z)))[mu* x.x >> match{Z => True >> print, S(y) => False >> print}]"
                     "Print(False)"

        --describe "Check if commands evaluate as expected with CBV:" $ do
        -- top-level CBN focusing at match
{-        evalFocusing CBN
                     "Ap(2)[mu* x. add >> 'Ap(x, x)[print]]  >> match{Ap(x)[k] => x >> k}"
                     "..."


comatch {Ap(x)[k] => Print(42)} >> Ap(2)[mu* x. add >> 'Ap(x)[print]]
--> error

-}