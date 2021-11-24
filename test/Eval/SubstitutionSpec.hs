module Eval.SubstitutionSpec where

import Control.Monad (forM_)
import Data.Map qualified as M
import Data.Text qualified as T
import Test.Hspec

import Pretty.Pretty
import Pretty.Errors ()
import Syntax.Terms
import Syntax.Program
import TestUtils
import TypeInference.Driver

spec :: Spec
spec = do
  describe "All examples are locally closed." $ do
    examples <- runIO $ getAvailableExamples "examples/"
    forM_ examples $ \example -> do
      describe ("Examples in " ++ example ++ " are locally closed") $ do
        env <- runIO $ getEnvironment example defaultInferenceOptions { infOptsLibPath = ["examples"] }
        case env of
          Left err -> it "Could not load examples." $ expectationFailure (ppPrintString err)
          Right env -> do
            forM_ (M.toList (prdEnv env)) $ \(name,(term,_,_)) -> do
              it (T.unpack name ++ " does not contain dangling deBruijn indizes") $
                termLocallyClosed term `shouldBe` Right ()

