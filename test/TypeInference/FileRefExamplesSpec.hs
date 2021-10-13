module TypeInference.FileRefExamplesSpec ( spec ) where

import           Test.Hspec
import           Control.Monad (forM_)

import TestUtils
import Pretty.Pretty
import Pretty.Errors ()
import TypeInference.GenerateConstraints.Definition ( InferenceMode(..) )
import TypeInference.Driver
-- | Typecheck the programs in the toplevel "examples-refined/" subfolder.
spec :: Spec
spec = do
  describe "All the programs in the toplevel \"examples-refined/\" folder typecheck." $ do
    examples <- runIO $ getAvailableExamples "examples-refined/"
    forM_ examples $ \example -> do
      describe ("The file " ++ example ++ " typechecks.") $ do
        env <- runIO $ getEnvironment example (defaultInferenceOptions { infOptsMode = InferRefined})
        case env of
          Left err -> it "Could not load examples" $ expectationFailure (ppPrintString err)
          Right _env -> return ()
