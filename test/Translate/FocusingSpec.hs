module Translate.FocusingSpec (spec) where

import Data.Bifunctor
import Data.Text (Text)
import qualified Data.Text as T
import Test.Hspec

import Parser.Parser
import Translate.Focusing

shouldFocusTo :: Text -- ^ The command that should be focused
              -> Text -- ^ The expected result of focusing
              -> Spec
shouldFocusTo input output = do
    it (T.unpack $ input <> " should focus to " <> output) $ do
        let Right (inputCmd,_)  = runInteractiveParser commandP input
        let Right (outputCmd,_) = runInteractiveParser commandP output
        let focusResult = focusCmd inputCmd
        focusResult `shouldBe` bimap (const ()) (const ()) outputCmd

-- Examples where Focusing should be a NoOp, since command is already
-- focused.
focusShouldBeNoOp :: Text -> Spec
focusShouldBeNoOp input = shouldFocusTo input input

spec :: Spec
spec = do
    describe "Static Focusing works" $ do        
        focusShouldBeNoOp "Done"
        focusShouldBeNoOp "S(Z) >> mu x.Done"
        focusShouldBeNoOp "Ap(5)[mu x.Done] >> mu y.Done"
        focusShouldBeNoOp "mu k.Done >> mu x.Done"
        focusShouldBeNoOp "Print(5)"
        "S(mu k.Z >> k) >> mu x.Done" `shouldFocusTo` "Done"
