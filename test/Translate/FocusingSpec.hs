module Translate.FocusingSpec (spec) where

import Control.Monad
import Test.Hspec
import TestUtils
import Pretty.Pretty
import Pretty.Program ()

import Driver.Definition
import Driver.Driver (inferProgramIO)
import Translate.Desugar
import Syntax.Common
import Syntax.CST.Program qualified as CST
import Translate.Focusing
import Translate.EmbedCore
import Translate.Reparse

testHelper :: FilePath -> EvaluationOrder -> SpecWith ()
testHelper example cbx = describe (show cbx ++ " Focusing the program in  " ++ example ++ " typechecks.") $ do
  decls <- runIO $ getTypecheckedDecls example
  case decls of
    Left err -> it "Could not read in example " $ expectationFailure (ppPrintString err)
    Right decls -> do
      let focusedDecls :: CST.Program = reparseProgram $ embedCoreProg $ focusProgram cbx (desugarProgram decls)
      res <- runIO $ inferProgramIO defaultDriverState (MkModuleName "") focusedDecls
      case res of
        Left err -> do
           let msg = unlines [ "---------------------------------"
                             , "Prettyprinted declarations:"
                             , ""
                             ,  ppPrintString (focusProgram cbx (desugarProgram decls))
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
        Right _env -> return ()

spec :: Spec
spec = do
    describe "Focusing an entire program still typechecks" $ do
      examples <- runIO $ getAvailableExamples "examples/"
      forM_ examples $ \example -> do
        testHelper example CBV
        testHelper example CBN
