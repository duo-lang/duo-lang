module Spec.Focusing (spec) where

import Control.Monad
import Data.List.NonEmpty ( NonEmpty )
import Test.Hspec
import Pretty.Pretty
import Pretty.Program ()

import Driver.Definition
import Driver.Driver (inferProgramIO)
import Translate.Embed
import Syntax.CST.Kinds
import Syntax.Common.Names
import Syntax.TST.Program qualified as TST
import Syntax.CST.Program qualified as CST
import Translate.Focusing
import Translate.Reparse
import Errors

type Reason = String

pendingFiles :: [(FilePath, Reason)]
pendingFiles = []

testHelper :: (FilePath, Either (NonEmpty Error) TST.Program) -> EvaluationOrder -> SpecWith ()
testHelper (example,decls) cbx = describe (show cbx ++ " Focusing the program in  " ++ example ++ " typechecks.") $ 
  case example `lookup` pendingFiles of
    Just reason -> it "" $ pendingWith $ "Could not focus file " ++ example ++ "\nReason: " ++ reason
    Nothing     -> 
      case decls of
        Left err -> it "Could not read in example " $ expectationFailure (ppPrintString err)
        Right decls -> do
          let focusedDecls :: CST.Program = reparseProgram $ embedCoreProg $ embedTSTProg $ focusProgram cbx decls
          res <- runIO $ inferProgramIO defaultDriverState (MkModuleName "Test:Focusing") focusedDecls
          case res of
            (Left err,_) -> do
              let msg = unlines [ "---------------------------------"
                                , "Prettyprinted declarations:"
                                , ""
                                ,  ppPrintString (focusProgram cbx decls)
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
              it "Could not load examples" $ expectationFailure msg
            (Right _env,_) -> pure ()

spec :: [(FilePath,Either (NonEmpty Error) TST.Program)] -> Spec
spec examples = do
    describe "Focusing an entire program still typechecks" $ do
      forM_ examples $ \example -> do
        testHelper example CBV
        testHelper example CBN
