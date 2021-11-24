module Translate.TranslateExamplesSpec ( spec ) where

import Control.Monad
import Test.Hspec

import Pretty.Pretty
import Pretty.Terms ()
import Pretty.Errors ()
import Syntax.CommonTerm
import Syntax.Program
import Translate.Translate 
import TypeInference.Driver
import TestUtils

spec :: Spec
spec = do
    describe "Desugaring an entire program still typechecks" $ do
      examples <- runIO $ getAvailableExamples "examples/"
      forM_ examples $ \example -> do
        describe ("Desugaring the program in  " ++ example ++ " typechecks.") $ do
          decls <- runIO $ getParsedDeclarations example
          case decls of
            Left err -> it "Could not parse example " $ expectationFailure (ppPrintString err)
            Right decls -> do
                let desugaredDecls :: Program Parsed = reParse $ compileProgram decls
                res <- runIO $ inferProgramIO (DriverState defaultInferenceOptions { infOptsLibPath = ["examples"] } mempty) desugaredDecls
                case res of
                    Left err -> it "Could not load examples" $ expectationFailure (ppPrintString err)
                    Right _env -> return ()

