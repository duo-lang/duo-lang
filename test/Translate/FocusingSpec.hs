module Translate.FocusingSpec (spec) where

import Control.Monad
import Test.Hspec
import TestUtils
import Pretty.Pretty

import TypeInference.Driver
import Translate.Desugar
import Parser.Parser
import Syntax.Terms
import Syntax.CommonTerm
import Syntax.Kinds
import Syntax.Program
import Translate.Focusing


spec :: Spec
spec = do
    describe "Focusing an entire program still typechecks" $ do
      examples <- runIO $ getAvailableExamples "examples/"
      forM_ examples $ \example -> do
        describe ("CBV Focusing the program in  " ++ example ++ " typechecks.") $ do
          decls <- runIO $ getParsedDeclarations example
          case decls of
            Left err -> it "Could not parse example " $ expectationFailure (ppPrintString err)
            Right decls -> do
                let focusedDecls :: Program Parsed = reParse $ focusProgram CBV (compileProgram decls)
                res <- runIO $ inferProgramIO (DriverState defaultInferenceOptions { infOptsLibPath = ["examples"] } mempty) focusedDecls
                case res of
                    Left err -> it "Could not load examples" $ expectationFailure (ppPrintString err)
                    Right _env -> return ()
        describe ("CBN Focusing the program in  " ++ example ++ " typechecks.") $ do
          decls <- runIO $ getParsedDeclarations example
          case decls of
            Left err -> it "Could not parse example " $ expectationFailure (ppPrintString err)
            Right decls -> do
                let focusedDecls :: Program Parsed = reParse $ focusProgram CBN (compileProgram decls)
                res <- runIO $ inferProgramIO (DriverState defaultInferenceOptions { infOptsLibPath = ["examples"] } mempty) focusedDecls
                case res of
                    Left err -> it "Could not load examples" $ expectationFailure (ppPrintString err)
                    Right _env -> return ()



