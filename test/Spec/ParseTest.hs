module Spec.ParseTest (spec) where

import Data.List.NonEmpty (NonEmpty)
import Test.Hspec

import Control.Monad.Except (runExceptT, MonadIO)
import Data.Either(isRight, fromRight)
import Driver.Definition (parseAndCheckModule)
import Errors
import Pretty.Pretty ( ppPrintString )
import Pretty.Errors ()
import Utils (moduleNameToFullPath)
import Syntax.CST.Names (ModuleName)
import Syntax.CST.Program qualified as CST


type Reason = String

pendingFiles :: [(ModuleName, Reason)]
pendingFiles = []

getParsedDeclarations :: MonadIO m => FilePath -> ModuleName -> m (Either (NonEmpty Error) CST.Module)
getParsedDeclarations fp mn = do
  let fullFp = moduleNameToFullPath mn fp
  runExceptT (parseAndCheckModule fullFp mn fp)



spec :: MonadIO m => (FilePath, ModuleName)
              -> m  (Maybe ((FilePath, ModuleName), CST.Module), Spec)
spec (fp, mn) = do
  prog <- getParsedDeclarations fp mn
  let fullName = moduleNameToFullPath mn fp
  case mn `lookup` pendingFiles of
    Just reason -> return (Nothing,
                          it "" $ pendingWith $ "Could not check Parse of file " ++ fullName ++ "\nReason: " ++ reason)
    Nothing -> do
        let pendingDescribe = describe ("The example " ++ fullName ++ " was parsed successfully")
        let msg = it "Was parsed."
        case prog of
              Left err -> return (Nothing, pendingDescribe (msg $ expectationFailure (ppPrintString err)))
              Right cst  -> return (Just ((fp, mn), cst), pendingDescribe (msg $ prog `shouldSatisfy` isRight))
