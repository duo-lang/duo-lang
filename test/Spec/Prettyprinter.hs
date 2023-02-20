module Spec.Prettyprinter (specParse, specType) where

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
specParse :: Monad m => ((FilePath, ModuleName), Either (NonEmpty Error) CST.Module)
              -> m (((FilePath, ModuleName), Either (NonEmpty Error) CST.Module), Spec)
specParse ((example, mn), prog) = do
  let fullName = moduleNameToFullPath mn example
  let msg = it "Can be parsed again."
  case prog of
        Left err     -> return (((example, mn), prog), msg $ expectationFailure (ppPrintString err))
        Right decls  -> do
          let test = runFileParser example (moduleP example) (ppPrint decls) ErrParser
          let pendingSpec = describe ("The example " ++ fullName ++ " can be parsed after prettyprinting.") $ do
                msg $ test `shouldSatisfy` isRight
          case test of
            Left err -> return (((example, mn),Left err), pendingSpec)
            Right _  -> return (((example, mn), prog), pendingSpec)


specType :: ((FilePath, ModuleName), Either (NonEmpty Error) TST.Module) -> Spec
specType ((example, mn), prog) = do
  let fullName = moduleNameToFullPath mn example
  describe ("The example " ++ fullName ++ " can be parsed after prettyprinting.") $ do
    case mn `lookup` pendingFiles of
      Just reason -> it "" $ pendingWith $ "Could not focus file " ++ fullName ++ "\nReason: " ++ reason
      Nothing     -> describe ("The example " ++ fullName ++ " can be parsed and typechecked after prettyprinting.") $ do
          let msg = it "Can be parsed and typechecked again."
          case prog of
            Left err -> msg $ expectationFailure (ppPrintString err)
            Right decls -> case runFileParser example (moduleP example) (ppPrint decls) ErrParser of
              Left _ -> msg $ expectationFailure "Could not be parsed"
              Right decls -> do
                res <- runIO $ inferProgramIO defaultDriverState decls
                msg $ fst res `shouldSatisfy` isRight

