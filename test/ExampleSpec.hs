module ExampleSpec where

import           Test.Hspec
import           Control.Monad (forM_, when)

import Data.Map (Map)
import qualified Data.Map as M

import Parser
import Syntax.Terms
import Syntax.Program
import Syntax.Types
import Utils
import Eval (isClosed_term, isLc_term)
import GenerateConstraints
import SolveConstraints
import TypeAutomata.Determinize
import TypeAutomata.FlowAnalysis
import TypeAutomata.Minimize (minimize)
import TypeAutomata.FromAutomaton

failingExamples :: [String]
failingExamples = ["div2and3"]

type TermEnvironment = Map FreeVarName (Term ())

getEnvironment :: IO TermEnvironment
getEnvironment = do
  s <- readFile "prg.txt"
  case runEnvParser environmentP mempty s of
    Right env -> return (M.filterWithKey (\k _ -> not (k `elem` failingExamples)) (prdEnv env <> cnsEnv env))
    Left _err -> error "Could not load prg.txt"

checkTerm :: (FreeVarName, Term ()) -> SpecWith ()
checkTerm (name,term) = it (name ++ " can be typechecked correctly") $ typecheckMaybe term `shouldBe` Nothing


typecheckMaybe :: Term () -> Maybe Error
typecheckMaybe t = case  typecheck t of
  Left err -> Just err
  Right _ -> Nothing

typecheck :: Term () -> Either Error TypeScheme
typecheck t = do
  (typedTerm, css, uvars) <- generateConstraints t
  typeAut <- solveConstraints css uvars (typedTermToType typedTerm) (termPrdOrCns t)
  let typeAutDet0 = determinize typeAut
  let typeAutDet = removeAdmissableFlowEdges typeAutDet0
  let minTypeAut = minimize typeAutDet
  return (autToType minTypeAut)

typecheckExample :: String -> String -> Spec
typecheckExample termS typS = do
  it (termS ++  " typechecks as: " ++ typS) $ do
      let Right term = runEnvParser (termP Prd) mempty termS
      let Right inferredType = typecheck term
      let Right specType = runEnvParser typeSchemeP mempty typS
      inferredType `shouldBe` specType

spec :: Spec
spec = do
  describe "All examples are closed" $ do
    env <- runIO getEnvironment
    when (failingExamples /= []) $ it "Some examples were ignored:" $ pendingWith $ unwords failingExamples
    forM_ (M.toList env) $ \(name,term) -> do
      it (name ++ " does not contain free variables") $ isClosed_term term `shouldBe` True
  describe "All examples are locally closed" $ do
    env <- runIO getEnvironment
    when (failingExamples /= []) $ it "Some examples were ignored:" $ pendingWith $ unwords failingExamples
    forM_ (M.toList env) $ \(name,term) -> do
      it (name ++ " does not contain dangling deBruijn indizes") $ isLc_term term `shouldBe` True
  describe "All examples typecheck" $ do
    env <- runIO getEnvironment
    when (failingExamples /= []) $ it "Some examples were ignored:" $ pendingWith $ unwords failingExamples
    forM_  (M.toList env) $ \term -> do
      checkTerm term
  describe "Typecheck specific examples" $ do
    typecheckExample "\\(x)[k] => x >> k" "forall t0. {- Ap(t0)[t0] -}"
    typecheckExample "S(Z)" "{+ S({+ Z +}) +}"
