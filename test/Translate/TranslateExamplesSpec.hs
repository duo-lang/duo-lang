module Translate.TranslateExamplesSpec ( spec ) where

import Test.Hspec
import Test.QuickCheck
import Control.Monad (forM_)


import TestUtils
import Parser.Parser
import Pretty.Pretty
import Syntax.STerms
import Syntax.ATerms
import Syntax.Types
import Syntax.Program
import Translate.Translate (compile)

-- | Compiles ATerms to STerms.
spec :: Spec
spec = do
  describe "Fetch examples in the toplevel \"examples/\" folder." $ do
    examples <- runIO getAvailableExamples
    forM_ examples $ \example -> do
      describe "compile function:" $ do
        it "translates ATerm 2 to STerm 2" $ 
          compile 2 `shouldBe` 2
		-- it "translates ATerm 'Cons 2' to STerm 'Cons 2'" $ do
        -- compile Cons (2) `shouldBe` Cons (2)
		