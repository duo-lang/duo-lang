module Spec.TypecheckTest (spec) where

import Data.List.NonEmpty (NonEmpty)
import Test.Hspec

import Control.Monad.Except (MonadIO, liftIO)
import Data.Either(isRight)
import Driver.Driver (inferProgramIO)
import Driver.Definition (defaultDriverState)
import Syntax.TST.Program qualified as TST
import Syntax.CST.Program qualified as CST
import Errors
import Pretty.Pretty ( ppPrintString )
import Pretty.Errors ()
import Utils (moduleNameToFullPath)
import Syntax.CST.Names (ModuleName (..))


type Reason = String

pendingFiles :: [(ModuleName, Reason)]
pendingFiles = []


getTypecheckedDecls :: (MonadIO m) => CST.Module -> m (Either (NonEmpty Error) TST.Module)
getTypecheckedDecls cst =
    fmap snd <$> (fst <$> liftIO (inferProgramIO defaultDriverState cst))



spec :: (MonadIO m) => ((FilePath, ModuleName), CST.Module)
              -> m (Maybe ((FilePath, ModuleName), TST.Module), Spec)
spec ((example, mn), cst) = do
  prog <- getTypecheckedDecls cst
  let fullName = moduleNameToFullPath mn example
  case mn `lookup` pendingFiles of
    Just reason -> return (Nothing, 
                           it "" $ pendingWith $ "Could not check Typechecking of file " ++ fullName ++ "\nReason: " ++ reason)
    Nothing -> do
      let pendingDescribe = describe ("The example " ++ fullName ++ " was typechecked successfully")
      let msg = it "Could be typechecked."
      case prog of
          Left err -> return (Nothing, pendingDescribe $ msg $ expectationFailure (ppPrintString err))
          Right cst  -> return (Just ((example, mn), cst), pendingDescribe $ msg $ prog `shouldSatisfy` isRight)
