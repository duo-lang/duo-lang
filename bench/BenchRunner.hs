module Main where

import Criterion.Main

import Control.Monad.Except
import Data.List.NonEmpty (NonEmpty)
import Driver.Definition (defaultDriverState, parseAndCheckModule)
import Driver.Driver (inferProgramIO)
import Errors
import Syntax.CST.Program qualified as CST
import Syntax.CST.Names
import Syntax.TST.Program qualified as TST
import Utils (listRecursiveDuoFiles, moduleNameToFullPath)

excluded :: [ModuleName]
excluded = []

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

getTypecheckedDecls :: FilePath -> ModuleName -> IO (Either (NonEmpty Error) TST.Module)
getTypecheckedDecls fp mn = do
  decls <- getParsedDeclarations fp mn
  case decls of
    Right decls -> do
      fmap snd <$> (fst <$> inferProgramIO defaultDriverState decls)
    Left err -> return (Left err)

typeInferenceBenchmarks :: [(FilePath, ModuleName)] -> Benchmark
typeInferenceBenchmarks fps = bgroup "Type inference" (uncurry inferType <$> fps)

inferType :: FilePath -> ModuleName -> Benchmark
inferType fp mn = bench (" Example: " <> moduleNameToFullPath mn fp) $ whnfIO (getTypecheckedDecls fp mn)

main :: IO ()
main = do
    examples <- getAvailableExamples
    defaultMain [typeInferenceBenchmarks examples]
