module Spec.Prettyprinter (spec) where

import Control.Monad (forM_)
import Data.Either (isRight)
import Test.Hspec

import Parser.Parser
import Pretty.Pretty
import Pretty.Errors ()
import Pretty.Program ()
import Syntax.Common
import Syntax.AST.Program qualified as AST
import Driver.Definition
import Driver.Driver
import Errors

-- Check that all the examples in `examples/..` can be:
-- 1. Parsed
-- 2. Prettyprinted
-- 3a. Parsed again from the prettyprinted result.
-- 3b. Parsed and typechecked again from the prettyprinted result.
spec :: [(FilePath, Either Error AST.Program)] -> Spec
spec examples = do
  describe "All the examples in the \"examples/\" folder can be parsed after prettyprinting." $ do
    forM_ examples $ \(example,prog) -> do
      describe ("The example " ++ example ++ " can be parsed after prettyprinting.") $ do
        it "Can be parsed again." $
          case prog of
            Left err -> expectationFailure (ppPrintString err)
            Right decls -> (runFileParser example programP (ppPrint decls)) `shouldSatisfy` isRight
  
  describe "All the examples in the \"examples/\" folder can be parsed and typechecked after prettyprinting." $ do
    forM_ examples $ \(example,prog) -> do
      describe ("The example " ++ example ++ " can be parsed and typechecked after prettyprinting.") $ do
        case prog of 
            Left err -> it "Can be parsed and typechecked again." $ expectationFailure (ppPrintString err)
            Right decls -> case (runFileParser example programP (ppPrint decls)) of
              Left _ -> it "Can be parsed and typechecked again." $ expectationFailure "Could not be parsed"
              Right decls -> do
                res <- runIO $ inferProgramIO defaultDriverState (MkModuleName "") decls
                it "Can be parsed and typechecked again." $
                    res `shouldSatisfy` isRight

