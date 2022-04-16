module Translate.TranslateExamplesSpec ( spec ) where

import Control.Monad
import Test.Hspec

import Pretty.Pretty
import Pretty.Terms ()
import Pretty.Errors ()
import Pretty.Program ()
import Syntax.Common
import Syntax.CST.Program qualified as CST
import Translate.Desugar
import Translate.EmbedCore
import Translate.Reparse
import Driver.Definition (defaultDriverState)
import Driver.Driver (inferProgramIO)
import TestUtils

spec :: [FilePath] -> Spec
spec examples = do
    describe "Desugaring an entire program still typechecks" $ do
      forM_ examples $ \example -> do
        describe ("Desugaring the program in  " ++ example ++ " typechecks.") $ do
          decls <- runIO $ getTypecheckedDecls example
          case decls of
            Left err -> it "Could not read in example " $ expectationFailure (ppPrintString err)
            Right decls -> do
              let desugaredDecls :: CST.Program = reparseProgram $ embedCoreProg $ desugarProgram decls
              res <- runIO $ inferProgramIO defaultDriverState (MkModuleName "") desugaredDecls
              case res of
                Left err -> do
                  let msg = unlines [ "---------------------------------"
                                    , "Prettyprinted declarations:"
                                    , ""
                                    ,  ppPrintString (embedCoreProg $ desugarProgram decls)
                                    , ""
                                    , "Show instance of declarations:"
                                    , ""
                                    , show desugaredDecls
                                    , ""
                                    , "Error message:"
                                    , ""
                                    , ppPrintString err
                                    , "---------------------------------"
                                    ]
                  it "Could not load examples" $ expectationFailure msg
                Right _env -> pure ()

