module TypeInference.CounterExampleSpec ( spec ) where

import Control.Monad (forM_)
import Data.Either (isLeft)
import Test.Hspec

import TestUtils
import Pretty.Pretty
import Syntax.Types
import TypeInference.GenerateConstraints.Definition ( InferenceMode(..) )
import TypeInference.InferProgram (defaultInferenceOptions)

instance Show (TypeScheme pol) where
  show = ppPrintString

-- | Check that the programs in "test/counterexamples/" subfolder dont typecheck.
spec :: Spec
spec = do
  describe "All the programs in the  \"test/counterexamples/\" folder don't typecheck." $ do
    examples <- runIO getAvailableCounterExamples
    forM_ examples $ \example -> do
      describe ("The counterexample " ++ example ++ " doesn't typecheck.") $ do
        env <- runIO $ getEnvironment example defaultInferenceOptions
        it "Doesn't typecheck" $  env `shouldSatisfy` isLeft


