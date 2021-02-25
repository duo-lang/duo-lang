module TypeInference.FileExamplesSpec ( spec ) where

import           Test.Hspec
import           Control.Monad (forM_, when)

import qualified Data.Map as M
import Data.Either (isRight)

import TestUtils
import Pretty.Pretty
import Syntax.STerms
import Syntax.Types
import Syntax.Program
import TypeInference.InferTypes

instance Show (TypeScheme pol) where
  show = ppPrint

failingExamples :: [String]
failingExamples = ["div2and3"]

checkTerm :: PrdCnsRep pc -> Environment -> (FreeVarName, STerm pc ()) -> SpecWith ()
checkTerm rep env (name,term) = it (name ++ " can be typechecked correctly") $ inferSTerm rep term env `shouldSatisfy` isRight

checkCommand :: Environment -> (FreeVarName, Command ()) -> SpecWith ()
checkCommand env (name,cmd) = it (name ++ " can be typechecked") $ checkCmd cmd env `shouldSatisfy` isRight

-- | Typecheck the programs in the toplevel "examples/" subfolder.
spec :: Spec
spec = do
  describe "All the programs in the toplevel \"examples/\" folder typecheck." $ do
    examples <- runIO getAvailableExamples
    forM_ examples $ \example -> do
      describe ("The file " ++ example ++ " typechecks.") $ do
        env <- runIO $ getEnvironment example failingExamples
        when (failingExamples /= []) $ it "Some examples were ignored:" $ pendingWith $ unwords failingExamples
        forM_  (M.toList (prdEnv env)) $ \term -> do
          checkTerm PrdRep env term
        forM_  (M.toList (cnsEnv env)) $ \term -> do
          checkTerm CnsRep env term
        forM_  (M.toList (cmdEnv env)) $ \cmd -> do
          checkCommand env cmd
