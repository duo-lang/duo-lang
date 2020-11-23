module Examples.ExampleSpec where

import           Test.Hspec
import           Control.Monad (forM_, when)

import qualified Data.Map as M

import Parser
import Syntax.Terms
import Utils
import Eval.Substitution (isClosed_term, isLc_term)
import GenerateConstraints
import SolveConstraints


failingExamples :: [String]
failingExamples = ["div2and3"]

getEnvironment :: IO TermEnvironment
getEnvironment = do
  s <- readFile "prg.txt"
  case runEnvParser environmentP M.empty s of
    Right env -> return (M.filterWithKey (\k _ -> not (k `elem` failingExamples)) env)
    Left _err -> error "Could not load prg.txt"

checkTerm :: (FreeVarName, Term ()) -> SpecWith ()
checkTerm (name,term) = it (name ++ " can be typechecked correctly") $ typecheck term `shouldBe` Nothing

typecheck :: Term () -> Maybe Error
typecheck t =
    case generateConstraints t of
      Right (typedTerm, css, uvars) -> case solveConstraints css uvars (typedTermToType typedTerm) (termPrdOrCns t) of
        Right _ -> Nothing
        Left err -> Just err
      Left err -> Just err

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
