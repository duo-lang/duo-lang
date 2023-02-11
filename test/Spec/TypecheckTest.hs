module Spec.TypecheckTest (spec) where

import Data.List.NonEmpty (NonEmpty)
import Test.Hspec

import Data.Either(isRight)
import Syntax.TST.Program qualified as TST
import Errors
import Pretty.Pretty ( ppPrintString )
import Pretty.Errors ()
import Utils (moduleNameToFullPath)
import Syntax.CST.Names (ModuleName)



spec :: ((FilePath, ModuleName), Either (NonEmpty Error) TST.Module) -> Spec
spec ((example, mn), prog) = do
  let fullName = moduleNameToFullPath mn example
  describe ("The example " ++ fullName ++ " was typechecked successfully") $ do
        it "Could be typechecked." $
          case prog of
            Left err -> expectationFailure (ppPrintString err)
            Right _ -> prog `shouldSatisfy` isRight