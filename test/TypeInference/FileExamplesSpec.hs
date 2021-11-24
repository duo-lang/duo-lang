module TypeInference.FileExamplesSpec ( spec ) where

import Test.Hspec
import Control.Monad (forM_)

import Data.Either( isRight, isLeft )
import TestUtils
import TypeInference.Driver

-- | Typecheck the programs in the toplevel "examples/" subfolder.
spec :: Spec
spec = do
  describe "All the programs in the toplevel \"examples/\" folder typecheck." $ do
    examples <- runIO $ getAvailableExamples "examples/"
    forM_ examples $ \example -> do
      env <- runIO $ getEnvironment example defaultInferenceOptions { infOptsLibPath = ["examples"] }
      it ("The file " ++ example ++ " typechecks.") $ do
        env `shouldSatisfy` isRight

  describe "All the programs in the  \"test/counterexamples/\" folder don't typecheck." $ do
    examples <- runIO getAvailableCounterExamples
    forM_ examples $ \example -> do
      describe ("The counterexample " ++ example ++ " doesn't typecheck.") $ do
        env <- runIO $ getEnvironment example defaultInferenceOptions
        it "Doesn't typecheck" $  env `shouldSatisfy` isLeft