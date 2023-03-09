module Spec.Prettyprinter (specParse, specType) where

import Data.Either (isRight)
import Data.List.NonEmpty ( NonEmpty )
import Test.Hspec
import Control.Monad.Except (MonadIO, liftIO)
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

getTypecheckedDecls :: (MonadIO m) => CST.Module -> m (Either (NonEmpty Error) TST.Module)
getTypecheckedDecls cst =
    fmap snd <$> (fst <$> liftIO (inferProgramIO defaultDriverState cst))

-- Check that all the examples in `examples/..` can be:
-- 1. Parsed
-- 2. Prettyprinted
-- 3a. Parsed again from the prettyprinted result.
-- 3b. Parsed and typechecked again from the prettyprinted result.
specParse :: Monad m => ((FilePath, ModuleName), CST.Module)
              -> m (Maybe ((FilePath, ModuleName), CST.Module), Spec)
specParse ((example, mn), prog) = do
  let fullName = moduleNameToFullPath mn example
  let msg = it "Can be parsed again."
  let test = runFileParser example (moduleP example) (ppPrint prog) ErrParser
  let pendingSpec = describe ("The example " ++ fullName ++ " can be parsed after prettyprinting.") $ do
        msg $ test `shouldSatisfy` isRight
  case test of
        Left _ -> return (Nothing, pendingSpec)
        Right _  -> return (Just ((example, mn), prog), pendingSpec)


specType :: (MonadIO m) => ((FilePath, ModuleName), TST.Module) 
                    -> m (Maybe ((FilePath, ModuleName), TST.Module), Spec)
specType ((fp, mn), prog) = do
  let fullName = moduleNameToFullPath mn fp
  let pendingDescribe = describe ("The example " ++ fullName ++ " can be parsed after prettyprinting.")
  case mn `lookup` pendingFiles of
    Just reason -> return (Nothing, pendingDescribe (it "" $ pendingWith $ "Could not Prettyprint file " ++ fullName ++ " after parsing. \nReason: " ++ reason))
    Nothing     -> do
        let msg = it "Can be parsed and typechecked again."
        let parse = runFileParser fp (moduleP fp) (ppPrint prog) ErrParser
        case parse of 
          Left _ -> return (Nothing, pendingDescribe (msg $ expectationFailure "Could not be parsed again"))
          Right decls -> do
            res <- getTypecheckedDecls decls
            case res of 
              Left _ -> return (Nothing, pendingDescribe (msg $ expectationFailure "Could not be typechecked again"))
              Right _ -> return (Just ((fp, mn), prog), pendingDescribe (msg $ res `shouldSatisfy` isRight))

