module TypeInference.FileExamplesSpec ( spec ) where

import           Test.Hspec
import           Control.Monad (forM_)

import TestUtils
import Pretty.Pretty
import Pretty.Errors ()
import TypeInference.InferProgram (defaultInferenceOptions, InferenceOptions (infOptsLibPath))

-- | Typecheck the programs in the toplevel "examples/" subfolder.
spec :: Spec
spec = do
  describe "All the programs in the toplevel \"examples/\" folder typecheck." $ do
    examples <- runIO $ getAvailableExamples "examples/"
    forM_ examples $ \example -> do
      describe ("The file " ++ example ++ " typechecks.") $ do
        env <- runIO $ getEnvironment example defaultInferenceOptions { infOptsLibPath = ["examples"] }
        case env of
          Left err -> it "Could not load examples" $ expectationFailure (ppPrintString err)
          Right _env -> return ()
