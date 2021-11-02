module Translate.FocusingSpec (spec) where

import Control.Monad
import Data.Text (Text)
import qualified Data.Text as T
import Test.Hspec
import TestUtils
import Pretty.Pretty

import TypeInference.Driver
import Translate.Translate
import Parser.Parser
import Syntax.STerms
import Syntax.Kinds
import Syntax.Program
import Translate.Focusing

import Unsafe.Coerce (unsafeCoerce)

shouldShiftTo :: STerm pc Compiled -> STerm pc Compiled -> Spec
shouldShiftTo tm1 tm2 = do
    it (ppPrintString tm1 <> " should shift to " <> ppPrintString tm2)  $ do
        shiftSTerm tm1 `shouldBe` tm2

shouldFocusTo :: Text -- ^ The command that should be focused
              -> Text -- ^ The expected result of focusing
              -> Spec
shouldFocusTo input output = do
    it (T.unpack $ input <> " should focus to " <> output) $ do
        let Right (inputCmd,_)  = runInteractiveParser commandP input
        let Right (outputCmd,_) = runInteractiveParser commandP output
        let focusResult = focusCmd CBV inputCmd
        removeNamesCmd focusResult `shouldBe` (removeNamesCmd $ compileCmd  outputCmd)

-- Examples where Focusing should be a NoOp, since command is already
-- focused.
focusShouldBeNoOp :: Text -> Spec
focusShouldBeNoOp input = shouldFocusTo input input

reParse :: Declaration ext -> Declaration Parsed
reParse = unsafeCoerce

focusExamples :: Spec
focusExamples = do
    examples <- runIO $ getAvailableExamples "examples/"
    forM_ examples $ \example -> do
      describe ("CBV Focusing the program in  " ++ example ++ " typechecks.") $ do
        decls <- runIO $ getParsedDeclarations example
        case decls of
            Left err -> it "Could not parse example " $ expectationFailure (ppPrintString err)
            Right decls -> do
                let focusedDecls :: Program Parsed = reParse <$> focusProgram CBV (compileDecl' <$> decls)
                res <- runIO $ inferProgramIO (DriverState defaultInferenceOptions { infOptsLibPath = ["examples"] } mempty) focusedDecls
                case res of
                    Left err -> it "Could not load examples" $ expectationFailure (ppPrintString err)
                    Right _env -> return ()
      describe ("CBN Focusing the program in  " ++ example ++ " typechecks.") $ do
        decls <- runIO $ getParsedDeclarations example
        case decls of
            Left err -> it "Could not parse example " $ expectationFailure (ppPrintString err)
            Right decls -> do
                let focusedDecls :: Program Parsed = reParse <$> focusProgram CBN (compileDecl' <$> decls)
                res <- runIO $ inferProgramIO (DriverState defaultInferenceOptions { infOptsLibPath = ["examples"] } mempty) focusedDecls
                case res of
                    Left err -> it "Could not load examples" $ expectationFailure (ppPrintString err)
                    Right _env -> return ()


spec :: Spec
spec = do
    describe "Shifting works" $ do
        (BoundVar () PrdRep (0,0)) `shouldShiftTo` (BoundVar () PrdRep (1,0))
        (BoundVar () PrdRep (10,0)) `shouldShiftTo` (BoundVar () PrdRep (11,0))
        (MuAbs () PrdRep Nothing (Done ())) `shouldShiftTo` (MuAbs () PrdRep Nothing (Done ()))
        (MuAbs () PrdRep Nothing (Apply () Nothing (BoundVar () PrdRep (0,0))(BoundVar () CnsRep (0,0)))) `shouldShiftTo` (MuAbs () PrdRep Nothing (Apply () Nothing (BoundVar () PrdRep (0,0))(BoundVar () CnsRep (0,0))))
        (MuAbs () PrdRep Nothing (Apply () Nothing (BoundVar () PrdRep (1,0))(BoundVar () CnsRep (1,0)))) `shouldShiftTo` (MuAbs () PrdRep Nothing (Apply () Nothing (BoundVar () PrdRep (2,0))(BoundVar () CnsRep (2,0))))
    describe "Static Focusing works on concrete examples" $ do
        focusShouldBeNoOp "Done"
        focusShouldBeNoOp "S(Z) >> mu x.Done"
        focusShouldBeNoOp "Ap(5)[mu x.Done] >> mu y.Done"
        focusShouldBeNoOp "mu k.Done >> mu x.Done"
        focusShouldBeNoOp "Print(5)"
        "S(mu k.Z >> k) >> mu x.Done"                   `shouldFocusTo` "mu alpha. ((mu k.Z >> k) >> mu x.(S(x) >> alpha)) >> mu x. Done"
        "Cons(mu k.Z >> k, mu r.Nil >> r) >> mu x.Done" `shouldFocusTo` "mu alpha.((mu k.Z >> k) >> mu res. (mu r. Nil >> r) >> mu res2. (Cons(res,res2) >> alpha))  >> mu x. Done"
        "mu a. (S(mu k. Z >> k) >> a) >> mu x. Done"    `shouldFocusTo` "mu a. (mu alpha. ((mu k.Z >> k) >> mu x.(S(x) >> alpha)) >> a) >> mu x.Done"
        "Z >> mu v.(S(mu k.Z >> k) >> v)"               `shouldFocusTo` "Z >> mu v. (mu alpha. ((mu k.Z >> k) >> mu x.(S(x) >> alpha)) >> v)"
    describe "Focusing an entire program still typechecks" $ do
        focusExamples

