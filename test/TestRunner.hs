module Main where

import Control.Monad.Except (runExceptT, forM, forM_)
import Control.Monad (when, foldM)
import Data.List.NonEmpty (NonEmpty(..))
import Data.List (sort)
import Data.Either (isRight)
import System.Environment (withArgs)
import Test.Hspec
import Test.Hspec.Runner
import Test.Hspec.Formatters
import GHC.IO.Encoding (setLocaleEncoding)
import System.IO (utf8)

import Driver.Definition (defaultDriverState, parseAndCheckModule)
import Driver.Driver (inferProgramIO)
import Errors
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

typecheckExamplesStandard :: [(a0, Either (NonEmpty Error) CST.Module)] -> IO [(a0, Either (NonEmpty Error) TST.Module)]
typecheckExamplesStandard examples =
  forM examples $ \(example, parse) -> do
    case parse of
      Left err -> pure (example, Left err)
      Right cst -> getTypecheckedDecls cst >>= \res -> pure (example, res)


typecheckExamplesCollectParsetree :: [(a0, Either (NonEmpty Error) CST.Module)] -> IO [(a0, Either (NonEmpty Error) (CST.Module, Either (NonEmpty Error) TST.Module))]
typecheckExamplesCollectParsetree examples =
  forM examples $ \(example, parse) -> do
    case parse of
      Left err -> pure (example, Left err)
      Right cst -> getTypecheckedDecls cst >>= \res -> pure (example, Right (cst, res))

------------------------------------------------------------------------------------------------------------------------

{-
-- Run Tests: A description, set of testvalues, a predicate (conditions for testing) and a spec test are needed
runner :: Description
            -> [a]
            -> (a -> Bool)
            -> (a -> Spec)
            -> Spec
runner descr exs p spec = do
  describe descr $ do
    forM_ exs $ \a -> Control.Monad.when (p a) $ spec a
-}

-- Monadrunner nimmt description, examples und predicate an, wie der normale runner. 
-- Allerdings muss jede spec Funktion jetzt ein Monad tuple ausgeben. Hier ist einmal der Spec, der von Hspec durchgeführt werden kann
-- und einmal b, das Ergebnis des Tests (Ergebnis = tuple, mit dem weitergearbeitet werden kann)
-- idealerweise ist das Ergebnis von runner ein tupel -> eine Liste, von Tests, die geklappt sind (bspw parses, die Funktionierten)
--                                                    -> Eine Abfolge von Specs, die im Anschluss durchgeführt werden können

runner :: Monad m
            => Description
            -> [(a, Either a1 b0)]
            -> ((a, Either a1 b0) -> Bool)
            -> ((a, Either a1 b0) -> m ((a, Either a1 b0), Spec))
            -> m ([(a, Either a1 b0)], Spec)
runner descr exs p spectest = do
  tested <- forM exs $ \a -> spectest a
  sequenced <- foldM f ([], return ()) tested
  case sequenced of
    (bs, specs) -> return (bs, describe descr specs)
  where f (bs, specsequence) (b, spec) = case snd b of
                                            Left _ -> return (bs, spec >> specsequence)
                                            Right _ -> return (b:bs, spec >> specsequence)


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
    typecheckedExamples <- typecheckExamplesStandard parsedExamples
    -- counterexamples 
    -- for the sake of the type inference test, they contain both the parse and the TST
    typecheckedCounterExamples <- typecheckExamplesCollectParsetree parsedCounterExamples

    --------------Collect specs----------------
    -- Parsetests
    successfullyParsedExamples <- runner "Examples could be successfully parsed" parsedExamples (const True) Spec.ParseTest.spec
    successfullyParsedCounterExamples <- runner "Counterexamples could be successfully parsed" parsedCounterExamples (const True) Spec.ParseTest.spec


    -- Prettyprinting after parsing: 
    parsedPPExamples <- runner "Prettyprinting and parsing again" (fst successfullyParsedExamples) (const True) Spec.Prettyprinter.specParse

    
    -- Locally closed (if examples are not locally closed, typechecking is naught): 
    locallyClosedExamples <- runner "Examples are locally closed" typecheckedExamples (const True) Spec.LocallyClosed.spec
    
    -- Typechecktest: 
    successfullyTypecheckedExamples <- runner "Examples could be successfully typechecked" (fst locallyClosedExamples) (const True) Spec.TypecheckTest.spec
    {-
    TODO: Rest of the tests
    -- Prettyprinting after typechecking: 
    typecheckedPPExamples <- runner "Examples parse and typecheck after prettyprinting" (fst successfullytypecheckedExamples) (const True) Spec.Prettyprinter.specType

    -- Focusing (makes only sense, if examples could be successfully typechecked):
    successfullyFocusedExamples <- runner "Examples can be focused" (fst successfullyTypecheckedExamples) (const True) Spec.Focusing.spec
    -}







    withArgs [] $ hspecWith defaultConfig { configFormatter = Just specdoc } $ do
      -- Tests before typechecking:
      snd successfullyParsedExamples
      snd successfullyParsedCounterExamples

      -- Tests after typechecking:
      snd parsedPPExamples
      snd locallyClosedExamples
      snd successfullyTypecheckedExamples  
      --snd typecheckedPPExamples
      --snd successfullyFocusedExamples
      -- Overlap Check: Not dependent on any parses:
      Spec.OverlapCheck.spec


