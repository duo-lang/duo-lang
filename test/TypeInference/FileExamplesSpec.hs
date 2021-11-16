module TypeInference.FileExamplesSpec ( spec ) where

import Test.Hspec
import Control.Monad (forM_)

import Data.Either( isRight)
import TestUtils
import Pretty.Pretty
import Pretty.Errors ()
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

