module Eval.SubstSpec ( spec )  where

import Test.Hspec

import Parser.Parser
import Pretty.Errors ()
import Syntax.STerms
import Eval.STerms (areAllSubst)
import Eval.Eval
import Control.Monad (forM_)


substCtorExample :: EvalOrder -> String -> Spec
substCtorExample order termS = do
  it (termS ++  " can't be substituted.") $ do
      let Right (term,_) = runInteractiveParser (stermP PrdRep) termS
      case term of
        XtorCall _ PrdRep _ args -> (areAllSubst order args) `shouldBe` False
        _ -> expectationFailure $ termS ++ "is not a Ctor."

cbvExamples :: [(EvalOrder,String)]
cbvExamples = 
    -- CBV examples
    zip
    (repeat CBV)
    [
    "C(mu x. 42 >> mu y. Print(y))[mu y. Print(y)]"
    , "C2(C(mu x. 42 >> mu y. Print(y))[mu y. Print(y)])"
    , "C(42)[D(mu x. Print(x))]"
    , "C( C(42)[D()[D2(mu x.Print(x))[]]])"
    , "C(42)[D()[D()[C(mu x. Print(x))[]]]]"
    ]

cbnExamples :: [(EvalOrder,String)]
cbnExamples = 
    -- CBN examples
    zip
    (repeat CBN)
    [
    "C('True)[mu x.Print(x)]"
    , "C('True)[D()[mu x. Print(x)]]"
    , "C(C(2)[mu x.Print(x)])[print]"
    , "C(C(2)[D()[mu x.Print(x)]])[print]"
    , "C(2)[C(2)[D(0)[mu x.Print(x)]]]"
    ]


spec :: Spec
spec = forM_ (cbvExamples ++ cbnExamples) $ uncurry substCtorExample
