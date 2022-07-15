module Spec.TypeInferenceExamples ( spec ) where

import Test.Hspec
import Control.Monad (forM_)

import Data.Either( isRight, isLeft )
import Syntax.TST.Program qualified as TST
import Syntax.CST.Program qualified as CST
import Errors

type Reason = String

pendingFiles :: [(FilePath, Reason)]
pendingFiles = [ ("examples/TypeClasses.ds", "Backend not implemented for type classes")
               ]

-- | Typecheck the programs in the toplevel "examples/" subfolder.
spec :: [(FilePath, Either Error TST.Program)] -- ^ examples
     -> [(FilePath, Either Error CST.Program)]
     -> [(FilePath, Either Error TST.Program)]
     -> Spec
spec examples counterExamplesParsed counterExamplesChecked = do
  describe "All the programs in the toplevel \"examples/\" folder typecheck." $ do
    forM_ examples $ \(example, prog) -> do
      case example `lookup` pendingFiles of
         Just reason -> it "" $ pendingWith $ "Could not focus file " ++ example ++ "\nReason: " ++ reason
         Nothing     -> it ("The file " ++ example ++ " typechecks.") $ prog `shouldSatisfy` isRight
  describe "All the programs in the \"test/counterexamples/\" folder can be parsed." $ do
    forM_ counterExamplesParsed $ \(example, prog) -> do
      describe ("The counterexample " ++ example ++ " can be parsed") $ do
        it "Can be parsed" $ prog `shouldSatisfy` isRight

  describe "All the programs in the \"test/counterexamples/\" folder don't typecheck." $ do
    forM_ counterExamplesChecked $ \(example,prog) -> do
      describe ("The counterexample " ++ example ++ " doesn't typecheck.") $ do
        it "Doesn't typecheck" $  prog `shouldSatisfy` isLeft
