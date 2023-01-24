module Spec.TypeInferenceExamples ( spec ) where

import Data.List.NonEmpty (NonEmpty)
import Test.Hspec
import Control.Monad (forM_)

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
spec :: ((FilePath, ModuleName), Either (NonEmpty Error) CST.Module)
     -> Either (NonEmpty Error) TST.Module
     -> Spec
spec ((example, mn), cst) tst = do
  let filePath = moduleNameToFullPath mn example
  case mn `lookup` pendingFiles of
    Just reason -> it "" $ pendingWith $ "Could not parse file " ++ filePath ++ "\nReason: " ++ reason
    Nothing     -> describe ("The counterexample " ++ filePath ++ " can be parsed") $ do
        it "Can be parsed" $ cst `shouldSatisfy` isRight

  case mn `lookup` pendingFiles of
    Just reason -> it "" $ pendingWith $ "Could not typecheck file " ++ filePath ++ "\nReason: " ++ reason
    Nothing     -> describe ("The counterexample " ++ filePath ++ " doesn't typecheck.") $ do
        it "Doesn't typecheck" $  tst `shouldSatisfy` isLeft
