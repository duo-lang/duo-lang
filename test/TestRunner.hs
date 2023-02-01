module Main where

import Control.Monad.Except (runExcept, runExceptT, forM, forM_)
import Data.List.NonEmpty (NonEmpty)
import Data.Either (isRight)
import Data.List (sort)
import System.Environment (withArgs)
import Test.Hspec
import Test.Hspec.Runner
import Test.Hspec.Formatters

import Driver.Definition (defaultDriverState, parseAndCheckModule)
import Driver.Driver (inferProgramIO)
import Errors
import Pretty.Pretty ( ppPrintString )
import Resolution.SymbolTable (SymbolTable, createSymbolTable)
import Spec.LocallyClosed qualified
import Spec.TypeInferenceExamples qualified
import Spec.OverlapCheck qualified
import Spec.Prettyprinter qualified
import Spec.Focusing qualified
import Syntax.CST.Program qualified as CST
import Syntax.CST.Names
import Syntax.TST.Program qualified as TST
import Options.Applicative
import Utils (listRecursiveDuoFiles, filePathToModuleName, moduleNameToFullPath)
import GHC.IO.Encoding (setLocaleEncoding)
import System.IO (utf8)

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

getTypecheckedDecls :: CST.Module -> IO (Either (NonEmpty Error) TST.Module)
getTypecheckedDecls cst =
    fmap snd <$> (fst <$> inferProgramIO defaultDriverState cst)


-- ? ---
getSymbolTable :: FilePath -> ModuleName -> IO (Either (NonEmpty Error) SymbolTable)
getSymbolTable fp mn = do
  decls <- getParsedDeclarations fp mn
  case decls of
    Right decls -> pure (runExcept (createSymbolTable decls))
    Left err -> return (Left err)
--------

parseExampleList :: [(FilePath, ModuleName)] -> IO [((FilePath, ModuleName), Either (NonEmpty Error) CST.Module)]
parseExampleList examples = do
  forM examples $ \example ->
    uncurry getParsedDeclarations example >>=
      \res -> pure (example, res)



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

    -- examples
    typecheckedExamples <- forM parsedExamples $ \(example, parse) -> do
      let fullName = moduleNameToFullPath (snd example) (fst example)
      withArgs [] $ hspecWith defaultConfig { configFormatter = Just specdoc } $ do
          describe ("Prettyprinting and parsing again " ++ fullName) (Spec.Prettyprinter.specParse (example, parse))
      case parse of
        Left err -> putStrLn (ppPrintString err) >> pure (example, Left err)
        Right cst -> getTypecheckedDecls cst >>= \res -> pure (example, res)

    forM_ typecheckedExamples $ \(example, tst) -> do
      case tst of
        Left err -> pure (example, Left err)
        Right typecheckResult -> do
          withArgs [] $ hspecWith defaultConfig { configFormatter = Just specdoc } $ do
              describe "example is locally closed" (Spec.LocallyClosed.spec (example, Right typecheckResult)) -- <- here not typechecking examples too?
              describe "Prettyprinting and parsing + typechecking again" (Spec.Prettyprinter.specType (example, Right typecheckResult))
              describe "Focusing works" (Spec.Focusing.spec (example, Right typecheckResult))
          pure (example, Right typecheckResult)

    -- counterexamples 
    forM_ parsedCounterExamples $ \(example, parse) -> do
      case parse of
        Left err -> pure (example, Left err)
        Right cst -> do
          typecheckedDecl <- getTypecheckedDecls cst >>= \res -> pure (example, res)
          let tst = snd typecheckedDecl
          case tst of
            Left err -> pure (example, Left err)
            Right typecheckResult -> do
              withArgs [] $ hspecWith defaultConfig { configFormatter = Just specdoc } $ do
                  describe "TypeInference with check" (Spec.TypeInferenceExamples.spec (example, parse) tst)
              pure (example, tst)
