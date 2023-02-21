module Spec.Focusing (spec) where

import Data.List.NonEmpty ( NonEmpty )
import Test.Hspec hiding (focus)

import Pretty.Pretty
import Pretty.Program ()
import Utils (moduleNameToFullPath)
import Control.Monad.Except (MonadIO, liftIO)
import Driver.Definition
import Driver.Driver (inferProgramIO)
import Sugar.Desugar (Desugar(..))
import Syntax.CST.Kinds
import Syntax.TST.Program qualified as TST
import Syntax.CST.Program qualified as CST
import Translate.Focusing
import Resolution.Unresolve
import Translate.EmbedTST (EmbedTST(..))
import Errors
import Syntax.CST.Names (ModuleName)

type Reason = String

pendingFiles :: [(ModuleName, Reason)]
pendingFiles = []

testHelper :: (MonadIO m) => ((FilePath, ModuleName), TST.Module) -> EvaluationOrder -> m (Maybe TST.Module, SpecWith ())
testHelper ((example, mn),decls) cbx = do 
  let pendingDescribe = describe (show cbx ++ " Focusing the program in  " ++ example ++ " typechecks.") 
  let fullName = moduleNameToFullPath mn example 
  case mn `lookup` pendingFiles of
    Just reason -> return (Nothing, pendingDescribe (it "" $ pendingWith $ "Could not focus file " ++ fullName ++ "\nReason: " ++ reason))
    Nothing     -> do
        let focusedDecls :: CST.Module = runUnresolveM $ unresolve $ embedCore $ embedTST $ focus cbx decls
        res <- fmap snd <$> (fst <$> liftIO (inferProgramIO defaultDriverState focusedDecls))
        case res of
          (Left err) -> do
            let msg = unlines [ "---------------------------------"
                              , "Prettyprinted declarations:"
                              , ""
                              ,  ppPrintString (focus cbx decls)
                              , ""
                              , "Show instance of declarations:"
                              , ""
                              , show focusedDecls
                              , ""
                              , "Error message:"
                              , ""
                              , ppPrintString err
                              , "---------------------------------"
                              ]
            return (Nothing, pendingDescribe (it "Could not load examples" $ expectationFailure msg))
          (Right _) -> return (Just decls, 
                               pendingDescribe (it ("Focused " ++ fullName ++ " succesfully") $ () `shouldBe` ()))

spec :: (MonadIO m) => ((FilePath, ModuleName), TST.Module) -> 
                   m (Maybe ((FilePath, ModuleName), TST.Module), Spec)
spec example = do
    testCBV <- testHelper example CBV
    testCBN <- testHelper example CBN
    let returnSpec = describe "Focusing an entire program still typechecks" $ do
                        snd testCBV
                        snd testCBN
    case (fst testCBV, fst testCBN) of
      (Just _, Just _) -> return (Just example, returnSpec)
      _                -> return (Nothing, returnSpec)
