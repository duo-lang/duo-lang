module Translate.FocusingSpec (spec) where

import Data.Bifunctor
import Data.Text (Text)
import qualified Data.Text as T
import Test.Hspec

import Parser.Parser
import Translate.Focusing

shouldFocusTo :: Text -> Text -> Spec
shouldFocusTo input output = do
    it (T.unpack $ input <> " should focus to " <> output) $ do
        let Right (inputCmd,_)  = runInteractiveParser commandP input
        let Right (outputCmd,_) = runInteractiveParser commandP output
        let focusResult = focusCmd inputCmd
        focusResult `shouldBe` first (const ()) outputCmd

spec :: Spec
spec = do
    describe "Static Focusing works" $ do
        "Done" `shouldFocusTo` "Done"
        "S(Z) >> mu x.Done" `shouldFocusTo` "S(Z) >> mu x.Done"
        "S(mu k.Z >> k) >> mu x.Done" `shouldFocusTo` "(mu k.Z >> k) >> mu res.(S(res) >> mu x.Done)"