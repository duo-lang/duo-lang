module Translate.TranslateProgramSpec ( spec ) where

import Test.Hspec
import Control.Monad (forM_)

import TestUtils
import Pretty.Pretty
import Pretty.Errors ()

-- | Translate the programs in the toplevel "examples/" subfolder to STerms.
spec :: Spec
spec = do
  describe "All the programs in the toplevel \"examples/\" folder translate to STerms." $ do
    examples <- runIO getAvailableExamples
    forM_ examples $ \example -> do
      describe ("The file " ++ example ++ " translates.") $ do
        env <- runIO $ getEnvironment example
        case env of
          Left err -> it "Could not load examples" $ expectationFailure (ppPrint err)
          Right _env -> return ()

-- TODO:
-- Copied body of spec from FileExamplesSpec.hs
-- need to adjust the body