module Translate.TranslateExamplesSpec ( spec ) where

import Control.Monad
import Test.Hspec

import Pretty.Pretty
import Pretty.Terms ()
import Pretty.Errors ()
import Syntax.CommonTerm
import Syntax.Program
import Translate.Desugar
import Translate.Reparse
import TypeInference.Driver
import TestUtils

driverState :: DriverState
driverState = DriverState defaultInferenceOptions { infOptsLibPath = ["examples"]} mempty

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
                inferredDecls <- runIO $ inferProgramIO driverState decls
                case inferredDecls of
                  Left err -> it "Could not typecheck example " $ expectationFailure (ppPrintString err)
                  Right (_,inferredDecls) -> do
                    let desugaredDecls :: Program Parsed = reparseProgram $ compileProgram inferredDecls
                    res <- runIO $ inferProgramIO driverState desugaredDecls
                    case res of
                        Left err -> it "Could not load examples" $ expectationFailure (ppPrintString err)
                        Right _env -> return ()

