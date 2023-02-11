module Spec.TypeInferenceExamples ( spec ) where

import Data.List.NonEmpty (NonEmpty)
import Test.Hspec

import Data.Either( isRight, isLeft )
import Syntax.TST.Program qualified as TST
import Syntax.CST.Program qualified as CST
import Errors
import Utils (moduleNameToFullPath)
import Syntax.CST.Names (ModuleName)

type Reason = String

pendingFiles :: [(ModuleName, Reason)]
pendingFiles = []

-- | Typecheck the programs in the toplevel "examples/" subfolder.
spec :: ((FilePath, ModuleName), Either (NonEmpty Error) (CST.Module, Either (NonEmpty Error) TST.Module))
     -> Spec
spec ((example, mn), cst) = do
  let filePath = moduleNameToFullPath mn example
  case mn `lookup` pendingFiles of
    Just reason -> it "" $ pendingWith $ "Could not parse file " ++ filePath ++ "\nReason: " ++ reason
    Nothing     -> describe ("The counterexample " ++ filePath ++ " can be parsed and typechecked") $ do
        it "Can be parsed" $ cst `shouldSatisfy` isRight
        case cst of
          Left _  -> pure ()
          Right (_, tst) -> it "Doesn't typecheck" $  tst `shouldSatisfy` isLeft
