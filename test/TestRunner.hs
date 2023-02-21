module Main where

import Control.Monad.Except (forM)
import Control.Monad (foldM)
import Data.List (sort)
import System.Environment (withArgs)
import Test.Hspec
import Test.Hspec.Runner
import Test.Hspec.Formatters
import GHC.IO.Encoding (setLocaleEncoding)
import System.IO (utf8)
import Spec.LocallyClosed qualified
import Spec.TypeInferenceExamples qualified
import Spec.OverlapCheck qualified
import Spec.Prettyprinter qualified
import Spec.Focusing qualified
import Spec.ParseTest qualified
import Spec.TypecheckTest qualified
import Syntax.CST.Names
import Options.Applicative
import Utils (listRecursiveDuoFiles, filePathToModuleName)

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

-- Monadrunner nimmt description, examples und predicate an, wie der normale runner. 
-- Allerdings muss jede spec Funktion jetzt ein Monad tuple ausgeben. Hier ist einmal der Spec, der von Hspec durchgeführt werden kann
-- und einmal b, das Ergebnis des Tests (Ergebnis = tuple, mit dem weitergearbeitet werden kann)
-- idealerweise ist das Ergebnis von runner ein tupel -> eine Liste, von Tests, die geklappt sind (bspw parses, die Funktionierten)
--                                                    -> Eine Abfolge von Specs, die im Anschluss durchgeführt werden können

runner :: Monad m
            => Description
            -> [a]
            -> (a -> m (Maybe b, Spec))
            -> m ([b], Spec)
runner descr exs spectest = do
  tested <- forM exs $ \a -> spectest a
  sequenced <- foldM f ([], return ()) tested
  case sequenced of
    (bs, specs) -> return (bs, describe descr specs)
  where f (bs, specsequence) (b, spec) = case b of
                                            Nothing -> return (bs, spec >> specsequence)
                                            Just x -> return (x:bs, spec >> specsequence)


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
    
    -- Typechecking: 
    --typecheckedExamples <- typecheckExamplesStandard parsedExamples
    -- counterexamples 
    -- for the sake of the type inference test, they contain both the parse and the TST
    --typecheckedCounterExamples <- typecheckExamplesCollectParsetree parsedCounterExamples

    --------------Collect specs----------------
    -- Collect the parsed declarations
    successfullyParsedExamples <- runner "Examples could be successfully parsed" examples Spec.ParseTest.spec
    successfullyParsedCounterExamples <- runner "Counterexamples could be successfully parsed" counterExamples Spec.ParseTest.spec

    -- Prettyprinting after parsing: 
    parsedPPExamples <- runner "Prettyprinting and parsing again" (fst successfullyParsedExamples) Spec.Prettyprinter.specParse
    
    -- Typechecktest: 
    successfullyTypecheckedExamples <- runner "Examples could be successfully typechecked" (fst successfullyParsedExamples) Spec.TypecheckTest.spec

    -- Locally closed (if examples are not locally closed, typechecking is naught): 
    locallyClosedExamples <- runner "Examples are locally closed" (fst successfullyTypecheckedExamples) Spec.LocallyClosed.spec
    
    
    
    -- Prettyprinting after typechecking: 
    typecheckedPPExamples <- runner "Examples parse and typecheck after prettyprinting" (fst successfullyTypecheckedExamples) Spec.Prettyprinter.specType

    -- Focusing (makes only sense, if examples could be successfully typechecked):
    successfullyFocusedExamples <- runner "Examples can be focused" (fst successfullyTypecheckedExamples) Spec.Focusing.spec

    -- Type Inference Test
    typeInferredCounterExamples <- runner "Counterexamples can be parsed but not typechecked" (fst successfullyParsedCounterExamples) Spec.TypeInferenceExamples.spec







    withArgs [] $ hspecWith defaultConfig { configFormatter = Just specdoc } $ do
      -- Tests before typechecking:
      snd successfullyParsedExamples
      snd successfullyParsedCounterExamples

      -- Tests after typechecking:
      snd parsedPPExamples
      snd locallyClosedExamples
      snd successfullyTypecheckedExamples  
      snd typecheckedPPExamples
      snd successfullyFocusedExamples
      snd typeInferredCounterExamples
      -- Overlap Check: Not dependent on any parses:
      Spec.OverlapCheck.spec


