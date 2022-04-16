module ParserPrettyprinter.ParserPrettyprinterSpec (spec) where

import Control.Monad (forM_)
import Data.Either (isRight)
import Test.Hspec

import Parser.Parser
import Pretty.Pretty
import Pretty.Errors ()
import Pretty.Program ()
import Syntax.Common
import TestUtils
import Driver.Definition
import Driver.Driver

-- Check that all the examples in `examples/..` can be:
-- 1. Parsed
-- 2. Prettyprinted
-- 3a. Parsed again from the prettyprinted result.
-- 3b. Parsed and typechecked again from the prettyprinted result.
spec :: [FilePath] -> Spec
spec examples = do
  describe "All the examples in the \"examples/\" folder can be parsed after prettyprinting." $ do
    forM_ examples $ \example -> do
      describe ("The example " ++ example ++ " can be parsed after prettyprinting.") $ do
        decls <- runIO $ getTypecheckedDecls example
        it "Can be parsed again." $
          case decls of
            Left err -> expectationFailure (ppPrintString err)
            Right decls -> (runFileParser example programP (ppPrint decls)) `shouldSatisfy` isRight
  
  describe "All the examples in the \"examples/\" folder can be parsed and typechecked after prettyprinting." $ do
    forM_ examples $ \example -> do
      describe ("The example " ++ example ++ " can be parsed and typechecked after prettyprinting.") $ do
        decls <- runIO $ getTypecheckedDecls example
        case decls of 
            Left err -> it "Can be parsed and typechecked again." $ expectationFailure (ppPrintString err)
            Right decls -> case (runFileParser example programP (ppPrint decls)) of
              Left _ -> it "Can be parsed and typechecked again." $ expectationFailure "Could not be parsed"
              Right decls -> do
                res <- runIO $ inferProgramIO defaultDriverState (MkModuleName "") decls
                it "Can be parsed and typechecked again." $
                    res `shouldSatisfy` isRight


