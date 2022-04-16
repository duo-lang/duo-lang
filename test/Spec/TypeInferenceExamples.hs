module Spec.TypeInferenceExamples ( spec ) where

import Test.Hspec
import Control.Monad (forM_)

import Data.Either( isRight, isLeft )
import Syntax.AST.Program qualified as AST
import Syntax.CST.Program qualified as CST
import Errors

-- | Typecheck the programs in the toplevel "examples/" subfolder.
spec :: [(FilePath, Either Error AST.Program)] -- ^ examples
     -> [(FilePath, Either Error CST.Program)]
     -> [(FilePath, Either Error AST.Program)]
     -> Spec
spec examples counterExamplesParsed counterExamplesChecked = do
  describe "All the programs in the toplevel \"examples/\" folder typecheck." $ do
    forM_ examples $ \(example, prog) -> do
      it ("The file " ++ example ++ " typechecks.") $ do
        prog `shouldSatisfy` isRight
  describe "All the programs in the \"test/counterexamples/\" folder can be parsed." $ do
    forM_ counterExamplesParsed $ \(example, prog) -> do
      describe ("The counterexample " ++ example ++ " can be parsed") $ do
        it "Can be parsed" $ prog `shouldSatisfy` isRight

  describe "All the programs in the \"test/counterexamples/\" folder don't typecheck." $ do
    forM_ counterExamplesChecked $ \(example,prog) -> do
      describe ("The counterexample " ++ example ++ " doesn't typecheck.") $ do
        it "Doesn't typecheck" $  prog `shouldSatisfy` isLeft