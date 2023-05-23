module Main where

import Data.List (sort)
import DependentTests
import Test.Hspec.Runner
import Test.Hspec.Formatters
import System.Environment (withArgs)
import GHC.IO.Encoding (setLocaleEncoding)
import System.IO (utf8)
import Spec.LocallyClosed qualified
import Spec.TypeInferenceExamples qualified
import Spec.Prettyprinter qualified
import Spec.Focusing qualified
import Spec.ParseTest qualified
import Spec.TypecheckTest qualified
import Syntax.CST.Names
import Options.Applicative
import Utils (listRecursiveDuoFiles, filePathToModuleName)
import Control.Monad.Reader
import Control.Monad.State

type Description = String

data TypeCheckMode = Standard | CollectParsetree

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

------------------------------------------------------------------------------------------------------------------------
testM :: [(FilePath, ModuleName)] -> [(FilePath, ModuleName)] -> TestM IO TestState
testM examples counterExamples = do
  
  ----------------------
  ----Perform Tests-----

  -- Collect the parsed declarations
  successfullyParsedExamples <- runTest "Examples could be successfully parsed" examples noDeps Spec.ParseTest.spec
  successfullyParsedCounterExamples <- runTest "Counterexamples could be successfully parsed" counterExamples noDeps Spec.ParseTest.spec

  -- Prettyprinting after parsing: 
  _parsedPPExamples <- runTestFromResult "Prettyprinting and parsing again" successfullyParsedExamples noDeps Spec.Prettyprinter.specParse
    
  -- Typechecktest: 
  successfullyTypecheckedExamples <- runTestFromResult "Examples could be successfully typechecked" successfullyParsedExamples noDeps Spec.TypecheckTest.spec

  -- Locally closed (if examples are not locally closed, typechecking is naught): 
  _locallyClosedExamples <- runTestFromResult "Examples are locally closed" successfullyTypecheckedExamples noDeps Spec.LocallyClosed.spec
    
    
    
  -- Prettyprinting after typechecking: 
  _typecheckedPPExamples <- runTestFromResult "Examples parse and typecheck after prettyprinting" successfullyTypecheckedExamples noDeps Spec.Prettyprinter.specType

  -- Focusing (makes only sense, if examples could be successfully typechecked):
  _successfullyFocusedExamples <- runTestFromResult "Examples can be focused" successfullyTypecheckedExamples noDeps Spec.Focusing.spec

  -- Type Inference Test
  _typeInferredCounterExamples <- runTestFromResult "Counterexamples cannot be typechecked" successfullyParsedCounterExamples noDeps Spec.TypeInferenceExamples.spec

  get

main :: IO ()
main = do
    setLocaleEncoding utf8

    -- Get examples ------
    o <- execParser getOpts
    examples <- case o of
      -- Collect the filepaths of all the available examples
      OptEmpty -> getAvailableExamples
      -- only use files specified in command line
      OptFilter fs -> pure $ (,) "." . filePathToModuleName <$> fs
    counterExamples <- getAvailableCounterExamples
    
    let config = DefConf
        testState = runReaderT (runTestM $ testM examples counterExamples) config

    finalState <- evalStateT testState initialTestState
    






    withArgs [] $ hspecWith defaultConfig { configFormatter = Just specdoc } $ do
      testSpecs finalState


