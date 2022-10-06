module Spec.Prettyprinter (spec) where

import Control.Monad (forM_)
import Data.Either (isRight)
import Data.List.NonEmpty ( NonEmpty )
import Test.Hspec

import Parser.Parser
import Pretty.Pretty
import Pretty.Errors ()
import Pretty.Program ()
import Syntax.CST.Program qualified as CST
import Syntax.TST.Program qualified as TST
import Driver.Definition
import Driver.Driver
import Errors
import Syntax.CST.Names (ModuleName(..))
import Utils (moduleNameToFullPath)

type Reason = String

pendingFiles :: [(ModuleName, Reason)]
pendingFiles = []

-- Check that all the examples in `examples/..` can be:
-- 1. Parsed
-- 2. Prettyprinted
-- 3a. Parsed again from the prettyprinted result.
-- 3b. Parsed and typechecked again from the prettyprinted result.
spec :: [((FilePath, ModuleName), Either (NonEmpty Error) CST.Module)] -- ^ examples to be parsed after pretty-printing
  -> [((FilePath, ModuleName), Either (NonEmpty Error) TST.Module)] -- ^ examples to be type-checked after pretty-printing
  -> Spec
spec parseExamples typeCheckExamples = do
  describe "All the examples in the \"examples/\" folder can be parsed after prettyprinting." $ do
    forM_ parseExamples $ \((example, mn) ,prog) -> do
      let fullName = moduleNameToFullPath mn example
      describe ("The example " ++ fullName ++ " can be parsed after prettyprinting.") $ do
        it "Can be parsed again." $
          case prog of
            Left err -> expectationFailure (ppPrintString err)
            Right decls -> runFileParser example (moduleP example) (ppPrint decls) `shouldSatisfy` isRight

  describe "All the examples in the \"examples/\" folder can be parsed and typechecked after prettyprinting." $ do
    forM_ typeCheckExamples $ \((example, mn), prog) -> do
      let fullName = moduleNameToFullPath mn example
      case mn `lookup` pendingFiles of
         Just reason -> it "" $ pendingWith $ "Could not focus file " ++ fullName ++ "\nReason: " ++ reason
         Nothing     -> describe ("The example " ++ fullName ++ " can be parsed and typechecked after prettyprinting.") $ do
            let msg = it "Can be parsed and typechecked again." 
            case prog of
                Left err -> msg $ expectationFailure (ppPrintString err)
                Right decls -> case runFileParser example (moduleP example) (ppPrint decls) of
                  Left _ -> msg $ expectationFailure "Could not be parsed"
                  Right decls -> do
                    res <- runIO $ inferProgramIO defaultDriverState decls
                    msg $ fst res `shouldSatisfy` isRight


