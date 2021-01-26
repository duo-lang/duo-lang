module ExampleSpec where

import           Test.Hspec
import           Control.Monad (forM_, when)

import qualified Data.Map as M
import Data.Either (isRight)

import TestUtils
import Parser.Parser
import Syntax.STerms
import Syntax.Program
import TypeInference.InferTypes
import TypeAutomata.ToAutomaton
import TypeAutomata.Subsume (typeAutEqual)

failingExamples :: [String]
failingExamples = ["div2and3"]

checkTerm :: Environment -> (FreeVarName, STerm Prd ()) -> SpecWith ()
checkTerm env (name,term) = it (name ++ " can be typechecked correctly") $ inferPrd term env `shouldSatisfy` isRight

typecheckExample :: Environment -> String -> String -> Spec
typecheckExample env termS typS = do
  it (termS ++  " typechecks as: " ++ typS) $ do
      let Right term = runEnvParser (stermP PrdRep) env termS
      let Right inferredTypeAut = inferPrdAut term env
      let Right specTypeScheme = runEnvParser typeSchemeP mempty typS
      let Right specTypeAut = typeToAut specTypeScheme
      (inferredTypeAut `typeAutEqual` specTypeAut) `shouldBe` True

spec :: Spec
spec = do
  describe "All examples typecheck." $ do
    examples <- runIO getAvailableExamples
    forM_ examples $ \example -> do
      describe ("Examples in " ++ example ++ " typecheck.") $ do
        env <- runIO $ getEnvironment example failingExamples
        when (failingExamples /= []) $ it "Some examples were ignored:" $ pendingWith $ unwords failingExamples
        forM_  (M.toList (prdEnv env)) $ \term -> do
          checkTerm env term
  describe "Typecheck specific examples" $ do
    env <- runIO $ getEnvironment "examples/prg.txt" []
    typecheckExample env "\\(x)[k] => x >> k" "forall a. { 'Ap(a)[a] }"
    typecheckExample env "'S('Z)" "< 'S(< 'Z >) >"
    typecheckExample env "\\(b,x,y)[k] => b >> match { 'True => x >> k, 'False => y >> k }"
                         "forall a. { 'Ap(< 'True | 'False >, a, a)[a] }"
    typecheckExample env "\\(b,x,y)[k] => b >> match { 'True => x >> k, 'False => y >> k }"
                         "forall a b. { 'Ap(<'True|'False>, a, b)[a \\/ b] }"
    typecheckExample env "\\(f)[k] => (\\(x)[k] => f >> 'Ap(x)[mu*y. f >> 'Ap(y)[k]]) >> k"
                         "forall a b. { 'Ap({ 'Ap(a \\/ b)[b] })[{ 'Ap(a)[b] }] }"
    -- Nominal Examples
    typecheckExample env "\\(x)[k] => x >> match { TT => FF >> k, FF => TT >> k }"
                         "{ 'Ap(Bool)[Bool] }"
    typecheckExample env "\\(x)[k] => x >> match { TT => FF >> k, FF => Zero >> k }"
                         "{ 'Ap(Bool)[(Bool \\/ Nat)] }"
    typecheckExample env "\\(x)[k] => x >> match { TT => FF >> k, FF => Zero >> k }"
                         "{ 'Ap(Bool)[(Nat \\/ Bool)] }"
    -- predNominal
    typecheckExample env "comatch { 'Ap(n)[k] => n >> match { Succ(m) => m >> k } }"
                         "{ 'Ap(Nat)[Nat] }"
    -- addNominal
    typecheckExample env "comatch { 'Ap(n,m)[k] => fix >> 'Ap( comatch { 'Ap(alpha)[k] => comatch { 'Ap(m)[k] => m >> match { Zero => n >> k, Succ(p) => alpha >> 'Ap(p)[mu* w. Succ(w) >> k] }} >> k })['Ap(m)[k]] }"
                         "forall t0. { 'Ap(t0,Nat)[(t0 \\/ Nat)] }"
    -- mltNominal
    typecheckExample env "comatch { 'Ap(n,m)[k] => fix >> 'Ap(comatch { 'Ap(alpha)[k] => comatch { 'Ap(m)[k] => m >> match { Zero => Zero >> k, Succ(p) => alpha >> 'Ap(p)[mu* w. addNominal >> 'Ap(n,w)[k]] } } >> k })['Ap(m)[k]]}"
                         "forall t0. { 'Ap((t0 /\\ Nat),Nat)[(t0 \\/ Nat)] }"
    -- expNominal
    typecheckExample env "comatch { 'Ap(n,m)[k] => fix >> 'Ap(comatch { 'Ap(alpha)[k] => comatch { 'Ap(m)[k] => m >> match { Zero => Succ(Zero) >> k, Succ(p) => alpha >> 'Ap(p)[mu* w. mltNominal >> 'Ap(n,w)[k]] } } >> k })['Ap(m)[k]] }"
                         "forall t0. { 'Ap((t0 /\\ Nat),Nat)[(t0 \\/ Nat)] }"
    -- subNominal
    typecheckExample env "comatch { 'Ap(n,m)[k] => fix >> 'Ap(comatch { 'Ap(alpha)[k] => comatch { 'Ap(m)[k] => m >> match { Zero => n >> k, Succ(p) => alpha >> 'Ap(p)[mu*w. predNominal >> 'Ap(w)[k]] }} >> k })['Ap(m)[k]] }"
                         "{ 'Ap(Nat,Nat)[Nat] }"
    -- subSafeNominal
    typecheckExample env "comatch { 'Ap(n,m)[k] => fix >> 'Ap(comatch { 'Ap(alpha)[k] => comatch { 'Ap(n)[k] => comatch { 'Ap(m)[k] => m >> match { Zero => n >> k, Succ(mp) => n >> match { Zero => n >> k, Succ(np) => alpha >> 'Ap(np)['Ap(mp)[k]] }}} >> k } >> k })['Ap(n)['Ap(m)[k]]]}"
                         "forall t0. { 'Ap((t0 /\\ Nat),Nat)[(t0 \\/ Nat)] }"

