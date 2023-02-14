module Main where

import Control.Monad.Except (runExcept, runExceptT, forM, forM_)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.List (sort)
import System.Environment (withArgs)
import Test.Hspec
import Test.Hspec.Runner
import Test.Hspec.Formatters
import GHC.IO.Encoding (setLocaleEncoding)
import System.IO (utf8)

import Driver.Definition (defaultDriverState, parseAndCheckModule)
import Driver.Driver (inferProgramIO)
import Errors
import Resolution.SymbolTable (SymbolTable, createSymbolTable)
import Spec.LocallyClosed qualified
import Spec.TypeInferenceExamples qualified
import Spec.OverlapCheck qualified
import Spec.Prettyprinter qualified
import Spec.Focusing qualified
import Spec.ParseTest qualified
import Spec.TypecheckTest qualified
import Syntax.CST.Program qualified as CST
import Syntax.CST.Names
import Syntax.TST.Program qualified as TST
import Options.Applicative
import Utils (listRecursiveDuoFiles, filePathToModuleName, moduleNameToFullPath)

type Description = String

data Options where
  OptEmpty  :: Options
  OptFilter :: [FilePath] -> Options

getOpts :: ParserInfo Options
getOpts = info (optsP <**> helper) mempty

optsP :: Parser Options
optsP = (OptFilter <$> filterP) <|> pure OptEmpty

filterP :: Parser [FilePath]
filterP = some (argument str (metavar "FILES..." <> help "Specify files which should be tested (instead of all in the `examples/` directory"))

getAvailableCounterExamples :: IO [(FilePath, ModuleName)]
getAvailableCounterExamples = do
  let counterExFp = "test/Counterexamples/"
  examples <- listRecursiveDuoFiles counterExFp
  pure  $ zip (repeat counterExFp) $ sort examples

excluded :: [ModuleName]
excluded = [MkModuleName [] "NestedPatternMatch"]

getAvailableExamples :: IO [(FilePath, ModuleName)]
getAvailableExamples = do
  let examplesFp  = "examples/"
  let examplesFp' = "std/"
  examples <- listRecursiveDuoFiles examplesFp
  examples' <- listRecursiveDuoFiles examplesFp'
  let examplesFiltered  = filter filterFun examples
  let examplesFiltered' = filter filterFun examples'
  return $ zip (repeat examplesFp) examplesFiltered ++ zip (repeat examplesFp') examplesFiltered'
    where
      filterFun s = s `notElem` excluded

getParsedDeclarations :: FilePath -> ModuleName -> IO (Either (NonEmpty Error) CST.Module)
getParsedDeclarations fp mn = do
  let fullFp = moduleNameToFullPath mn fp
  runExceptT (parseAndCheckModule fullFp mn fp)

parseExampleList :: [(FilePath, ModuleName)] -> IO [((FilePath, ModuleName), Either (NonEmpty Error) CST.Module)]
parseExampleList examples = do
  forM examples $ \example ->
    uncurry getParsedDeclarations example >>=
      \res -> pure (example, res)

getTypecheckedDecls :: CST.Module -> IO (Either (NonEmpty Error) TST.Module)
getTypecheckedDecls cst =
    fmap snd <$> (fst <$> inferProgramIO defaultDriverState cst)


-- ? ---
getSymbolTable :: FilePath -> ModuleName -> IO (Either (NonEmpty Error) SymbolTable)
getSymbolTable fp mn = do
  decls <- getParsedDeclarations fp mn
  case decls of
    Right decls -> case (runExcept (createSymbolTable decls)) of
      Left err -> pure (Left (ErrResolution err :| []))
      Right res -> pure (pure res)
    Left err -> return (Left err)
--------

runSpecTest :: Description
            -> [(a0, Either (NonEmpty Error) b0)]
            -> ((a0, Either (NonEmpty Error) b0) -> Spec)
            -> Spec
runSpecTest description examples spec = do
  describe description $ do
    forM_ examples $ \(example, syntaxtree) ->
      case syntaxtree of
        Left _ -> pure ()
        Right res -> spec (example, Right res)

-- As the successtest checks whether the syntaxtree was parsed successfully or not, 
-- runSpecTest can't be used
runSuccessTest :: Description
              -> [(a0, Either (NonEmpty Error) b0)]
              -> ((a0, Either (NonEmpty Error) b0) -> Spec)
              -> Spec
runSuccessTest description examples spec = do
  describe description $ do
    forM_ examples $ \(example, syntaxtree) ->
      spec (example, syntaxtree)






main :: IO ()
main = do
    setLocaleEncoding utf8
    o <- execParser getOpts
    examples <- case o of
      -- Collect the filepaths of all the available examples
      OptEmpty -> getAvailableExamples
      -- only use files specified in command line
      OptFilter fs -> pure $ (,) "." . filePathToModuleName <$> fs
    counterExamples <- getAvailableCounterExamples
    -- Collect the parsed declarations
    parsedExamples <- parseExampleList examples
    parsedCounterExamples <- parseExampleList counterExamples





    -- Typechecking: 
    typecheckedExamples <- forM parsedExamples $ \(example, parse) -> do
      case parse of
        Left err -> pure (example, Left err)
        Right cst -> getTypecheckedDecls cst >>= \res -> pure (example, res)

    -- counterexamples 
    -- for the sake of the type inference test, they contain both the parse and the TST
    typecheckedCounterExamples <- forM parsedCounterExamples $ \(example, parse) -> do
      case parse of
        Left err -> pure (example, Left err)
        Right cst -> getTypecheckedDecls cst >>= \res -> pure (example, Right (cst, res))


    withArgs [] $ hspecWith defaultConfig { configFormatter = Just specdoc } $ do
    -- Tests before typechecking:
      runSuccessTest "Examples could be successfully parsed" parsedExamples Spec.ParseTest.spec
      runSpecTest "Prettyprinting and parsing again" parsedExamples Spec.Prettyprinter.specParse
    -- Tests after typechecking:
      runSuccessTest "Examples could be successfully typechecked" typecheckedExamples Spec.TypecheckTest.spec
      runSpecTest "Examples parse and typecheck after prettyprinting" typecheckedExamples Spec.Prettyprinter.specType
      runSpecTest "Examples are locally closed" typecheckedExamples Spec.LocallyClosed.spec  -- <- TODO: Only typechecking is dependent on local closedness
      runSpecTest "Examples can be focused" typecheckedExamples Spec.Focusing.spec
      runSpecTest "TypeInference with check" typecheckedCounterExamples Spec.TypeInferenceExamples.spec
      -- Overlap Check: Not dependent on any parses:
      Spec.OverlapCheck.spec


