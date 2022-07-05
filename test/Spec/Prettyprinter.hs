module Spec.Prettyprinter (spec) where

import Control.Monad (forM_)
import Data.Either (isRight)
import Test.Hspec

import Parser.Parser
import Pretty.Pretty
import Pretty.Errors ()
import Pretty.Program ()
import Syntax.Common
import Syntax.CST.Program qualified as CST
import Syntax.TST.Program qualified as TST
import Driver.Definition
import Driver.Driver
import Errors

type Reason = String

pendingFiles :: [(FilePath, Reason)]
pendingFiles = [ ("examples/TypeClasses.ds", "Backend not implemented for type classes")
               , ("examples/TypeClassInstance.ds", "Backend not implemented for type classes")
               ]

-- Check that all the examples in `examples/..` can be:
-- 1. Parsed
-- 2. Prettyprinted
-- 3a. Parsed again from the prettyprinted result.
-- 3b. Parsed and typechecked again from the prettyprinted result.
spec :: [(FilePath, Either Error CST.Program)] -- ^ examples to be parsed after pretty-printing
  -> [(FilePath, Either Error TST.Program)] -- ^ examples to be type-checked after pretty-printing
  -> Spec
spec parseExamples typeCheckExamples = do
  describe "All the examples in the \"examples/\" folder can be parsed after prettyprinting." $ do
    forM_ parseExamples $ \(example,prog) -> do
      describe ("The example " ++ example ++ " can be parsed after prettyprinting.") $ do
        it "Can be parsed again." $
          case prog of
            Left err -> expectationFailure (ppPrintString err)
            Right decls -> runFileParser example programP (ppPrint decls) `shouldSatisfy` isRight

  describe "All the examples in the \"examples/\" folder can be parsed and typechecked after prettyprinting." $ do
    forM_ typeCheckExamples $ \(example,prog) -> do
      case example `lookup` pendingFiles of
         Just reason -> it "" $ pendingWith $ "Could not focus file " ++ example ++ "\nReason: " ++ reason
         Nothing     -> describe ("The example " ++ example ++ " can be parsed and typechecked after prettyprinting.") $ do
            case prog of
                Left err -> it "Can be parsed and typechecked again." $ expectationFailure (ppPrintString err)
                Right decls -> case runFileParser example programP (ppPrint decls) of
                  Left _ -> it "Can be parsed and typechecked again." $ expectationFailure "Could not be parsed"
                  Right decls -> do
                    res <- runIO $ inferProgramIO defaultDriverState (MkModuleName "") decls
                    it "Can be parsed and typechecked again." $
                        res `shouldSatisfy` isRight


