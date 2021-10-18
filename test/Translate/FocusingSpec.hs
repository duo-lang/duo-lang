module Translate.FocusingSpec (spec) where

import Control.Monad
import Data.Bifunctor
import Data.Text (Text)
import qualified Data.Text as T
import Test.Hspec
import TestUtils
import Pretty.Pretty
import Utils

import TypeInference.Driver
import Parser.Parser
import Translate.Focusing
import Eval.Eval

shouldFocusTo :: Text -- ^ The command that should be focused
              -> Text -- ^ The expected result of focusing
              -> Spec
shouldFocusTo input output = do
    it (T.unpack $ input <> " should focus to " <> output) $ do
        let Right (inputCmd,_)  = runInteractiveParser commandP input
        let Right (outputCmd,_) = runInteractiveParser commandP output
        let focusResult = focusCmd CBV inputCmd
        focusResult `shouldBe` bimap (const ()) (const ()) outputCmd

-- Examples where Focusing should be a NoOp, since command is already
-- focused.
focusShouldBeNoOp :: Text -> Spec
focusShouldBeNoOp input = shouldFocusTo input input

focusExamples :: Spec
focusExamples = do
    examples <- runIO $ getAvailableExamples "examples/"
    forM_ examples $ \example -> do
      describe ("CBV Focusing the program in  " ++ example ++ " typechecks.") $ do
        decls <- runIO $ getParsedDeclarations example
        case decls of
            Left err -> it "Could not parse example " $ expectationFailure (ppPrintString err)
            Right decls -> do
                let focusedDecls = bimap (const "x") (const defaultLoc) <$> (focusProgram CBV (bimap (const ()) (const ()) <$> decls))
                res <- runIO $ inferProgramIO (DriverState defaultInferenceOptions { infOptsLibPath = ["examples"] } mempty) focusedDecls
                case res of
                    Left err -> it "Could not load examples" $ expectationFailure (ppPrintString err)
                    Right _env -> return ()
      describe ("CBN Focusing the program in  " ++ example ++ " typechecks.") $ do
        decls <- runIO $ getParsedDeclarations example
        case decls of
            Left err -> it "Could not parse example " $ expectationFailure (ppPrintString err)
            Right decls -> do
                let focusedDecls = bimap (const "x") (const defaultLoc) <$> (focusProgram CBN (bimap (const ()) (const ()) <$> decls))
                res <- runIO $ inferProgramIO (DriverState defaultInferenceOptions { infOptsLibPath = ["examples"] } mempty) focusedDecls
                case res of
                    Left err -> it "Could not load examples" $ expectationFailure (ppPrintString err)
                    Right _env -> return ()


spec :: Spec
spec = do
    describe "Static Focusing works on concrete examples" $ do        
        focusShouldBeNoOp "Done"
        focusShouldBeNoOp "S(Z) >> mu x.Done"
        focusShouldBeNoOp "Ap(5)[mu x.Done] >> mu y.Done"
        focusShouldBeNoOp "mu k.Done >> mu x.Done"
        focusShouldBeNoOp "Print(5)"
        "S(mu k.Z >> k) >> mu x.Done" `shouldFocusTo` "mu alpha. ((mu k.Z >> k) >> mu x.(S(x) >> alpha)) >> mu x. Done"
        "Cons(mu k.Z >> k, mu r.Nil >> r) >> mu x.Done" `shouldFocusTo` "mu alpha.((mu k.Z >> k) >> mu res. (mu r. Nil >> r) >> mu res2. (Cons(res,res2) >> alpha))  >> mu x. Done"
    describe "Focusing an entire program still typechecks" $ do
        focusExamples

