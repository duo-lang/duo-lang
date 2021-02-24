module TypeInference.CounterExampleSpec ( spec ) where

import Control.Monad (forM_)
import Data.Either (isLeft)
import qualified Data.Map as M
import Test.Hspec

import TestUtils
import Pretty.Pretty
import Syntax.STerms
import Syntax.Types
import Syntax.Program
import TypeInference.InferTypes

instance Show (TypeScheme pol) where
  show = ppPrint

checkPrd :: Environment -> (FreeVarName, STerm Prd ()) -> SpecWith ()
checkPrd env (name,term) = it (name ++ " doesn't typecheck") $ inferPrd term env `shouldSatisfy` isLeft

-- | Check that the programs in "test/counterexamples/" subfolder dont typecheck.
spec :: Spec
spec = do
  describe "All the programs in the  \"test/counterexamples/\" folder don't typecheck." $ do
    examples <- runIO getAvailableCounterExamples
    forM_ examples $ \example -> do
      describe ("The counterexample " ++ example ++ " doesn't typecheck.") $ do
        env <- runIO $ getEnvironment example []
        forM_  (M.toList (prdEnv env)) $ \prd -> do
          checkPrd env prd

