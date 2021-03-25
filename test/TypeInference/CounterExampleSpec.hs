module TypeInference.CounterExampleSpec ( spec ) where

import Control.Monad (forM_)
import Data.Either (isLeft)
import Test.Hspec

import TestUtils
import Pretty.Pretty
import Syntax.Types

instance Show (TypeScheme pol) where
  show = ppPrint

-- | Check that the programs in "test/counterexamples/" subfolder dont typecheck.
spec :: Spec
spec = do
  describe "All the programs in the  \"test/counterexamples/\" folder don't typecheck." $ do
    examples <- runIO getAvailableCounterExamples
    forM_ examples $ \example -> do
      describe ("The counterexample " ++ example ++ " doesn't typecheck.") $ do
        env <- runIO $ getEnvironment example
        it "Doesn't typecheck" $  env `shouldSatisfy` isLeft


