module Spec.Focusing (spec) where

import Control.Monad
import Test.Hspec
import Pretty.Pretty
import Pretty.Program ()

import Driver.Definition
import Driver.Driver (inferProgramIO)
import Sugar.Desugar
import Sugar.Resugar
import Syntax.Common
import Syntax.AST.Program qualified as AST
import Syntax.CST.Program qualified as CST
import Translate.Focusing
import Translate.Reparse
import Errors

testHelper :: (FilePath, Either Error AST.Program) -> EvaluationOrder -> SpecWith ()
testHelper (example,decls) cbx = describe (show cbx ++ " Focusing the program in  " ++ example ++ " typechecks.") $ do
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
        Right _env -> pure ()

spec :: [(FilePath,Either Error AST.Program)] -> Spec
spec examples = do
    describe "Focusing an entire program still typechecks" $ do
      forM_ examples $ \example -> do
        testHelper example CBV
        testHelper example CBN
