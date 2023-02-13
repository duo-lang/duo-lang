module Spec.ParseTest (spec) where

import Data.List.NonEmpty (NonEmpty)
import Test.Hspec

import Data.Either(isRight)
import Syntax.CST.Program qualified as CST
import Errors
import Pretty.Pretty ( ppPrintString )
import Pretty.Errors ()
import Utils (moduleNameToFullPath)
import Syntax.CST.Names (ModuleName)


type Reason = String

pendingFiles :: [(ModuleName, Reason)]
pendingFiles = []

spec :: ((FilePath, ModuleName), Either (NonEmpty Error) CST.Module) -> Spec
spec ((example, mn), prog) = do
  let fullName = moduleNameToFullPath mn example
  case mn `lookup` pendingFiles of
    Just reason -> it "" $ pendingWith $ "Could check local closure of file " ++ fullName ++ "\nReason: " ++ reason
    Nothing -> 
      describe ("The example " ++ fullName ++ " was parsed successfully") $ do
            it "Was parsed." $
              case prog of
                Left err -> expectationFailure (ppPrintString err)
                Right _ -> prog `shouldSatisfy` isRight
