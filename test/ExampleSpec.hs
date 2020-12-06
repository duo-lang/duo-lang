module ExampleSpec where

import           Test.Hspec
import           Control.Monad (forM_, when)

import Data.Map (Map)
import qualified Data.Map as M

import Parser
import Syntax.Terms
import Syntax.Program
import Syntax.TypeGraph
import Utils
import Eval (isClosed_term, isLc_term)
import GenerateConstraints
import SolveConstraints
import TypeAutomata.Determinize
import TypeAutomata.FlowAnalysis
import TypeAutomata.Minimize (minimize)
import TypeAutomata.ToAutomaton
import TypeAutomata.Subsume (typeAutEqual)

failingExamples :: [String]
failingExamples = ["div2and3"]

filterEnvironment :: Environment -> Environment
filterEnvironment Environment {..} = Environment { prdEnv = M.filterWithKey (\k _ -> not (k `elem` failingExamples)) prdEnv
                                                 , cnsEnv = M.filterWithKey (\k _ -> not (k `elem` failingExamples)) cnsEnv
                                                 , typEnv = typEnv
                                                 }

getEnvironment :: IO Environment
getEnvironment = do
  s <- readFile "prg.txt"
  case runEnvParser environmentP mempty s of
    Right env -> return (filterEnvironment env) --() (prdEnv env <> cnsEnv env))
    Left _err -> error "Could not load prg.txt"

checkTerm :: (FreeVarName, Term Prd ()) -> SpecWith ()
checkTerm (name,term) = it (name ++ " can be typechecked correctly") $ typecheckMaybe term `shouldBe` Nothing


typecheckMaybe :: Term Prd () -> Maybe Error
typecheckMaybe t = case  typecheck t of
  Left err -> Just err
  Right _ -> Nothing

typecheck :: Term Prd () -> Either Error TypeAutDet
typecheck t = do
  (typedTerm, css, uvars) <- generateConstraints t
  typeAut <- solveConstraints css uvars (typedTermToType typedTerm) Prd
  let typeAutDet0 = determinize typeAut
  let typeAutDet = removeAdmissableFlowEdges typeAutDet0
  let minTypeAut = minimize typeAutDet
  return minTypeAut

typecheckExample :: String -> String -> Spec
typecheckExample termS typS = do
  it (termS ++  " typechecks as: " ++ typS) $ do
      let Right term = runEnvParser (termP PrdRep) mempty termS
      let Right inferredTypeAut = typecheck term
      let Right specTypeScheme = runEnvParser typeSchemeP mempty typS
      let Right specTypeAut = typeToAut specTypeScheme
      (inferredTypeAut `typeAutEqual` specTypeAut) `shouldBe` True

spec :: Spec
spec = do
  describe "All examples are closed" $ do
    env <- runIO getEnvironment
    when (failingExamples /= []) $ it "Some examples were ignored:" $ pendingWith $ unwords failingExamples
    forM_ (M.toList (prdEnv env)) $ \(name,term) -> do
      it (name ++ " does not contain free variables") $ isClosed_term term `shouldBe` True
  describe "All examples are locally closed" $ do
    env <- runIO getEnvironment
    when (failingExamples /= []) $ it "Some examples were ignored:" $ pendingWith $ unwords failingExamples
    forM_ (M.toList (prdEnv env)) $ \(name,term) -> do
      it (name ++ " does not contain dangling deBruijn indizes") $ isLc_term term `shouldBe` True
  describe "All examples typecheck" $ do
    env <- runIO getEnvironment
    when (failingExamples /= []) $ it "Some examples were ignored:" $ pendingWith $ unwords failingExamples
    forM_  (M.toList (prdEnv env)) $ \term -> do
      checkTerm term
  describe "Typecheck specific examples" $ do
    typecheckExample "\\(x)[k] => x >> k" "forall a. {- Ap(a)[a] -}"
    typecheckExample "S(Z)" "{+ S({+ Z +}) +}"
    typecheckExample "\\(b,x,y)[k] => b >> {+ True => x >> k, False => y >> k +}"
                     "forall a. {- Ap({+True,False+}, a, a)[a] -}"
    typecheckExample "\\(b,x,y)[k] => b >> {+ True => x >> k, False => y >> k +}"
                     "forall a b. {- Ap({+True,False+}, a, b)[a \\/ b] -}"
    typecheckExample "\\(f)[k] => (\\(x)[k] => f >> Ap(x)[mu*y. f >> Ap(y)[k]]) >> k"
                     "forall a b. {- Ap({- Ap(a \\/ b)[b] -})[{- Ap(a)[b] -}] -}"
