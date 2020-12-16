module ExampleSpec where

import           Test.Hspec
import           Control.Monad (forM_, when)

import qualified Data.Map as M

import TestUtils
import Parser
import Syntax.Terms
import Syntax.Program
import Syntax.TypeGraph
import Utils
import GenerateConstraints
import SolveConstraints
import TypeAutomata.Determinize
import TypeAutomata.FlowAnalysis
import TypeAutomata.Minimize (minimize)
import TypeAutomata.ToAutomaton
import TypeAutomata.Subsume (typeAutEqual)

failingExamples :: [String]
failingExamples = ["div2and3"]

checkTerm :: Environment -> (FreeVarName, Term Prd ()) -> SpecWith ()
checkTerm env (name,term) = it (name ++ " can be typechecked correctly") $ typecheckMaybe env term `shouldBe` Nothing


typecheckMaybe :: Environment -> Term Prd () -> Maybe Error
typecheckMaybe env t = case typecheck env t of
  Left err -> Just err
  Right _ -> Nothing

typecheck :: Environment -> Term Prd () -> Either Error TypeAutDet
typecheck env t = do
  (typedTerm, css, uvars) <- generateConstraints t env
  typeAut <- solveConstraints css uvars (typedTermToType env typedTerm) Prd
  let typeAutDet0 = determinize typeAut
  let typeAutDet = removeAdmissableFlowEdges typeAutDet0
  let minTypeAut = minimize typeAutDet
  return minTypeAut

typecheckExample :: Environment -> String -> String -> Spec
typecheckExample env termS typS = do
  it (termS ++  " typechecks as: " ++ typS) $ do
      let Right term = runEnvParser (termP PrdRep) mempty termS
      let Right inferredTypeAut = typecheck env term
      let Right specTypeScheme = runEnvParser typeSchemeP mempty typS
      let Right specTypeAut = typeToAut specTypeScheme
      (inferredTypeAut `typeAutEqual` specTypeAut) `shouldBe` True

spec :: Spec
spec = do
  describe "All examples typecheck" $ do
    env <- runIO $ getEnvironment "prg.txt" failingExamples
    when (failingExamples /= []) $ it "Some examples were ignored:" $ pendingWith $ unwords failingExamples
    forM_  (M.toList (prdEnv env)) $ \term -> do
      checkTerm env term
  describe "Typecheck specific examples" $ do
    env <- runIO $ getEnvironment "prg.txt" []
    typecheckExample env "\\(x)[k] => x >> k" "forall a. { 'Ap(a)[a] }"
    typecheckExample env "'S('Z)" "< 'S(< 'Z >) >"
    typecheckExample env "\\(b,x,y)[k] => b >> match { 'True => x >> k, 'False => y >> k }"
                         "forall a. { 'Ap(< 'True | 'False >, a, a)[a] }"
    typecheckExample env "\\(b,x,y)[k] => b >> match { 'True => x >> k, 'False => y >> k }"
                         "forall a b. { 'Ap(<'True|'False>, a, b)[a \\/ b] }"
    typecheckExample env "\\(f)[k] => (\\(x)[k] => f >> 'Ap(x)[mu*y. f >> 'Ap(y)[k]]) >> k"
                         "forall a b. { 'Ap({ 'Ap(a \\/ b)[b] })[{ 'Ap(a)[b] }] }"
