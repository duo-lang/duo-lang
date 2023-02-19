module Spec.TypecheckTest (spec) where

import Data.List.NonEmpty (NonEmpty)
import Test.Hspec

import Data.Either(isRight)
import Syntax.TST.Program qualified as TST
import Errors
import Pretty.Pretty ( ppPrintString )
import Pretty.Errors ()
import Utils (moduleNameToFullPath)
import Syntax.CST.Names (ModuleName (..))


type Reason = String

pendingFiles :: [(ModuleName, Reason)]
pendingFiles = [(  MkModuleName [] "ListRefinement" ,"Type Applications to Refinement Types aren't fully implemented yet"), (MkModuleName [] "Refinements", "Type Applications to Refinement Types aren't fully implemented yet")]

spec :: Monad m => ((FilePath, ModuleName), Either (NonEmpty Error) TST.Module)
              -> m (((FilePath, ModuleName), Either (NonEmpty Error) TST.Module), Spec)
spec ((example, mn), prog) = do
  let fullName = moduleNameToFullPath mn example
  case mn `lookup` pendingFiles of
    Just reason -> return (((example, mn), prog), 
                           it "" $ pendingWith $ "Could not check Typechecking of file " ++ fullName ++ "\nReason: " ++ reason)
    Nothing -> do
      let returnSpec =  describe ("The example " ++ fullName ++ " was typechecked successfully") $ do
            it "Could be typechecked." $
              case prog of
                Left err -> expectationFailure (ppPrintString err)
                Right _ -> prog `shouldSatisfy` isRight
      return (((example, mn), prog), returnSpec)
