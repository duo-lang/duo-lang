module Translate.FocusingSpec (spec) where

import Control.Monad
import Test.Hspec
import TestUtils
import Pretty.Pretty

import TypeInference.Driver
import Translate.Desugar
import Syntax.Common
import Syntax.Kinds
import Syntax.AST.Program
import Translate.Focusing
import Translate.Reparse


driverState :: DriverState
driverState = DriverState defaultInferenceOptions { infOptsLibPath = ["examples"]} mempty

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
                inferredDecls <- runIO $ inferProgramIO driverState decls
                case inferredDecls of
                  Left err -> it "Could not typecheck example " $ expectationFailure (ppPrintString err)
                  Right (_,inferredDecls) -> do
                    let focusedDecls :: Program Parsed = reparseProgram $ focusProgram CBV (desugarProgram inferredDecls)
                    res <- runIO $ inferProgramIO driverState focusedDecls
                    case res of
                        Left err -> it "Could not load examples" $ expectationFailure (ppPrintString err)
                        Right _env -> return ()
        describe ("CBN Focusing the program in  " ++ example ++ " typechecks.") $ do
          decls <- runIO $ getParsedDeclarations example
          case decls of
            Left err -> it "Could not parse example " $ expectationFailure (ppPrintString err)
            Right decls -> do
                inferredDecls <- runIO $ inferProgramIO driverState decls
                case inferredDecls of
                  Left err -> it "Could not typecheck example " $ expectationFailure (ppPrintString err)
                  Right (_,inferredDecls) -> do
                    let focusedDecls :: Program Parsed = reparseProgram $ focusProgram CBN (desugarProgram inferredDecls)
                    res <- runIO $ inferProgramIO driverState focusedDecls
                    case res of
                        Left err -> it "Could not load examples" $ expectationFailure (ppPrintString err)
                        Right _env -> return ()
