module ParserPrettyprinter.ParserPrettyprinterSpec (spec) where

import Control.Monad (forM_)
import Data.Either (isRight)
import Test.Hspec

import Parser.Parser
import Pretty.Pretty
import Pretty.Errors ()
import Pretty.Program ()
import TestUtils

-- Check that all the examples in `examples/..` can be:
-- 1. Parsed
-- 2. Prettyprinted
-- 3. Parsed again from the prettyprinted result.
spec :: Spec
spec = do
  describe "All the examples in the \"examples/\" folder can be parsed after prettyprinting." $ do
    examples <- runIO getAvailableExamples
    forM_ examples $ \example -> do
      describe ("The example " ++ example ++ " can be parsed after prettyprinting.") $ do
        decls <- runIO $ getParsedDeclarations example
        it "Can be parsed again." $
          case decls of
            Left err -> expectationFailure (ppPrint err)
            Right decls -> (runFileParser example programP (ppPrint decls)) `shouldSatisfy` isRight


