module Spec.TypeInferenceExamples ( spec ) where

import Data.List.NonEmpty (NonEmpty)
import Test.Hspec
import Control.Monad (forM_)

import Data.Either( isRight, isLeft )
import Syntax.TST.Program qualified as TST
import Syntax.CST.Program qualified as CST
import Errors

-- | Typecheck the programs in the toplevel "examples/" subfolder.
spec :: [(FilePath, Either (NonEmpty Error) CST.Program)]
     -> [(FilePath, Either (NonEmpty Error) TST.Program)]
     -> Spec
spec counterExamplesParsed counterExamplesChecked = do
  describe "All the programs in the \"test/counterexamples/\" folder can be parsed." $ do
    forM_ counterExamplesParsed $ \(example, prog) -> do
      describe ("The counterexample " ++ example ++ " can be parsed") $ do
        it "Can be parsed" $ prog `shouldSatisfy` isRight

  describe "All the programs in the \"test/counterexamples/\" folder don't typecheck." $ do
    forM_ counterExamplesChecked $ \(example,prog) -> do
      describe ("The counterexample " ++ example ++ " doesn't typecheck.") $ do
        it "Doesn't typecheck" $  prog `shouldSatisfy` isLeft
