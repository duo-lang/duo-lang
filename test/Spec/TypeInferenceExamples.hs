module Spec.TypeInferenceExamples ( spec ) where

import Data.List.NonEmpty (NonEmpty)
import Test.Hspec
import Control.Monad (forM_)

import Data.Either( isRight, isLeft )
import Syntax.TST.Program qualified as TST
import Syntax.CST.Program qualified as CST
import Errors

type Reason = String

pendingFiles :: [(FilePath, Reason)]
pendingFiles = [ ("test/counterexamples/CE_053.duo", "Constraint Solver for type class methods not implemented yet.")
               ]

-- | Typecheck the programs in the toplevel "examples/" subfolder.
spec :: [(FilePath, Either (NonEmpty Error) CST.Module)]
     -> [(FilePath, Either (NonEmpty Error) TST.Module)]
     -> Spec
spec counterExamplesParsed counterExamplesChecked = do
  describe "All the programs in the \"test/counterexamples/\" folder can be parsed." $ do
    forM_ counterExamplesParsed $ \(example, prog) -> do
      case example `lookup` pendingFiles of
        Just reason -> it "" $ pendingWith $ "Could not parse file " ++ example ++ "\nReason: " ++ reason
        Nothing     -> describe ("The counterexample " ++ example ++ " can be parsed") $ do
          it "Can be parsed" $ prog `shouldSatisfy` isRight

  describe "All the programs in the \"test/counterexamples/\" folder don't typecheck." $ do
    forM_ counterExamplesChecked $ \(example,prog) -> do
      case example `lookup` pendingFiles of
        Just reason -> it "" $ pendingWith $ "Could not typecheck file " ++ example ++ "\nReason: " ++ reason
        Nothing     -> describe ("The counterexample " ++ example ++ " doesn't typecheck.") $ do
          it "Doesn't typecheck" $  prog `shouldSatisfy` isLeft
