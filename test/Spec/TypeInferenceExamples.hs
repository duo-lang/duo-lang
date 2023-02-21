module Spec.TypeInferenceExamples ( spec ) where

import Data.List.NonEmpty (NonEmpty)
import Test.Hspec
import Control.Monad.Except (MonadIO, liftIO)
import Data.Either( isRight, isLeft )
import Driver.Driver (inferProgramIO)
import Driver.Definition (defaultDriverState)
import Syntax.TST.Program qualified as TST
import Syntax.CST.Program qualified as CST
import Errors
import Utils (moduleNameToFullPath)
import Syntax.CST.Names (ModuleName)

type Reason = String

pendingFiles :: [(ModuleName, Reason)]
pendingFiles = []

getTypecheckedDecls :: (MonadIO m) => CST.Module -> m (Either (NonEmpty Error) TST.Module)
getTypecheckedDecls cst =
    fmap snd <$> (fst <$> liftIO (inferProgramIO defaultDriverState cst))

-- | Typecheck the programs in the toplevel "examples/" subfolder.
spec :: (MonadIO m) => ((FilePath, ModuleName), CST.Module)
        -> m (Maybe ((FilePath, ModuleName), CST.Module), Spec)
spec ((example, mn), cst) = do
  let filePath = moduleNameToFullPath mn example
  let pendingDescribe = describe ("The counterexample " ++ filePath ++ " can be parsed and doesn't typecheck")
  case mn `lookup` pendingFiles of
    Just reason -> return (Nothing, 
                          pendingDescribe (it "" $ pendingWith $ "Could not parse file " ++ filePath ++ "\nReason: " ++ reason))
    Nothing     -> do 
        res <- getTypecheckedDecls cst
        let returnSpec = pendingDescribe $ it "Can be parsed and does not typecheck" $ res `shouldSatisfy` isLeft
        case res of
            Left _  -> return (Just ((example, mn), cst), returnSpec)
            Right _ -> return (Nothing, returnSpec)
