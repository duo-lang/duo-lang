module Eval.SubstitutionSpec where

import Control.Monad (forM_)
import Data.Either (isLeft, isRight)
import qualified Data.Map as M
import qualified Data.Text as T
import Test.Hspec



import Pretty.Pretty
import Pretty.Errors ()
import Syntax.STerms
import Syntax.Program
import TypeInference.GenerateConstraints.Definition ( InferenceMode(..) )
import Utils
import TestUtils

spec :: Spec
spec = do
  describe "All examples are locally closed." $ do
    examples <- runIO $ getAvailableExamples "examples/"
    forM_ examples $ \example -> do
      describe ("Examples in " ++ example ++ " are locally closed") $ do
        env <- runIO $ getEnvironment example InferNominal
        case env of
          Left err -> it "Could not load examples." $ expectationFailure (ppPrintString err)
          Right env -> do
            forM_ (M.toList (prdEnv env)) $ \(name,(term,_)) -> do
              it (T.unpack name ++ " does not contain dangling deBruijn indizes") $
                termLocallyClosed term `shouldBe` Right ()

  describe "checkIfBound works" $ do
    it "checkIfBound [] PrdRep (0,0) `shouldBe` False" $ do
      checkIfBound [] PrdRep (0,0) `shouldSatisfy` isLeft
    it "checkIfBound [Twice [] []] PrdRep (0,0) = False" $ do
      checkIfBound [Twice [] []] PrdRep (0,0) `shouldSatisfy` isLeft
    it "checkIfBound [Twice [()] []] PrdRep (0,0) = True" $ do
      checkIfBound [Twice [()] []] PrdRep (0,0) `shouldSatisfy` isRight
    it "checkIfBound [Twice [] [()]] CnsRep (0,0) = True" $ do
      checkIfBound [Twice [] [()]] CnsRep (0,0) `shouldSatisfy` isRight
    it "checkIfBound [Twice [()] []] CnsRep (0,0) = False" $ do
      checkIfBound [Twice [()] []] CnsRep (0,0) `shouldSatisfy` isLeft

