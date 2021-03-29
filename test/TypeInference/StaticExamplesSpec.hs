module TypeInference.StaticExamplesSpec ( spec )  where

import Test.Hspec

import TestUtils
import Parser.Parser
import Pretty.Pretty
import Syntax.STerms
import Syntax.Types
import Syntax.Program
import TypeInference.InferTypes
import TypeAutomata.ToAutomaton
import TypeAutomata.Subsume (typeAutEqual)

instance Show (TypeScheme pol) where
  show = ppPrint

typecheckExample :: Environment FreeVarName -> String -> String -> Spec
typecheckExample env termS typS = do
  it (termS ++  " typechecks as: " ++ typS) $ do
      let Right term = runInteractiveParser (stermP PrdRep) termS
      let Right inferredTypeAut = inferSTermAut PrdRep term env
      let Right specTypeScheme = runInteractiveParser typeSchemeP typS
      let Right specTypeAut = typeToAut specTypeScheme
      (inferredTypeAut `typeAutEqual` specTypeAut) `shouldBe` True

spec :: Spec
spec = do
  describe "Typecheck specific examples" $ do
    env <- runIO $ getEnvironment "examples/prg.ds"
    case env of
      Left err -> it "Could not load environment" $ expectationFailure (ppPrint err)
      Right env' -> do
        typecheckExample env' "\\(x)[k] => x >> k" "forall a. { 'Ap(a)[a] }"
        typecheckExample env' "'S('Z)" "< 'S(< 'Z >) >"
        typecheckExample env' "\\(b,x,y)[k] => b >> match { 'True => x >> k, 'False => y >> k }"
                             "forall a. { 'Ap(< 'True | 'False >, a, a)[a] }"
        typecheckExample env' "\\(b,x,y)[k] => b >> match { 'True => x >> k, 'False => y >> k }"
                             "forall a b. { 'Ap(<'True|'False>, a, b)[a \\/ b] }"
        typecheckExample env' "\\(f)[k] => (\\(x)[k] => f >> 'Ap(x)[mu*y. f >> 'Ap(y)[k]]) >> k"
                             "forall a b. { 'Ap({ 'Ap(a \\/ b)[b] })[{ 'Ap(a)[b] }] }"
        -- Nominal Examples
        typecheckExample env' "\\(x)[k] => x >> match { TT => FF >> k, FF => TT >> k }"
                             "{ 'Ap(Bool)[Bool] }"
        typecheckExample env' "\\(x)[k] => x >> match { TT => FF >> k, FF => Z >> k }"
                             "{ 'Ap(Bool)[(Bool \\/ Nat)] }"
        typecheckExample env' "\\(x)[k] => x >> match { TT => FF >> k, FF => Z >> k }"
                             "{ 'Ap(Bool)[(Nat \\/ Bool)] }"
        -- addNominal
        typecheckExample env' "comatch { 'Ap(n,m)[k] => fix >> 'Ap( comatch { 'Ap(alpha)[k] => comatch { 'Ap(m)[k] => m >> match { Z => n >> k, S(p) => alpha >> 'Ap(p)[mu* w. S(w) >> k] }} >> k })['Ap(m)[k]] }"
                             "forall t0. { 'Ap(t0,Nat)[(t0 \\/ Nat)] }"
        -- mltNominal
        typecheckExample env' "comatch { 'Ap(n,m)[k] => fix >> 'Ap(comatch { 'Ap(alpha)[k] => comatch { 'Ap(m)[k] => m >> match { Z => Z >> k, S(p) => alpha >> 'Ap(p)[mu* w. addNominal >> 'Ap(n,w)[k]] } } >> k })['Ap(m)[k]]}"
                             "forall t0. { 'Ap((t0 /\\ Nat),Nat)[(t0 \\/ Nat)] }"
        -- expNominal
        typecheckExample env' "comatch { 'Ap(n,m)[k] => fix >> 'Ap(comatch { 'Ap(alpha)[k] => comatch { 'Ap(m)[k] => m >> match { Z => S(Z) >> k, S(p) => alpha >> 'Ap(p)[mu* w. mltNominal >> 'Ap(n,w)[k]] } } >> k })['Ap(m)[k]] }"
                             "forall t0. { 'Ap((t0 /\\ Nat),Nat)[(t0 \\/ Nat)] }"
        -- subSafeNominal
        typecheckExample env' "comatch { 'Ap(n,m)[k] => fix >> 'Ap(comatch { 'Ap(alpha)[k] => comatch { 'Ap(n)[k] => comatch { 'Ap(m)[k] => m >> match { Z => n >> k, S(mp) => n >> match { Z => n >> k, S(np) => alpha >> 'Ap(np)['Ap(mp)[k]] }}} >> k } >> k })['Ap(n)['Ap(m)[k]]]}"
                             "forall t0. { 'Ap((t0 /\\ Nat),Nat)[(t0 \\/ Nat)] }"

