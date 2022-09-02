module Main where

import Criterion.Main

import Control.Monad.Except
import Data.List.NonEmpty (NonEmpty)
import Data.Text.IO qualified as T
import Driver.Definition (defaultDriverState)
import Driver.Driver (inferProgramIO)
import Errors
import Parser.Definition (runFileParser)
import Parser.Program (moduleP)
import Resolution.SymbolTable (SymbolTable, createSymbolTable)
import Syntax.CST.Program qualified as CST
import Syntax.TST.Program qualified as TST
import Options.Applicative
import Utils (listRecursiveDuoFiles)


import Utils ( listRecursiveDuoFiles )

excluded :: [FilePath]
excluded = ["fix.duo"]

getAvailableExamples :: IO [FilePath]
getAvailableExamples = do
  examples <- listRecursiveDuoFiles "examples/"
  examples' <- listRecursiveDuoFiles "std/"
  return (filter (\s -> head s /= '.' && notElem s excluded) (examples <> examples'))

getParsedDeclarations :: FilePath -> IO (Either (NonEmpty Error) CST.Module)
getParsedDeclarations fp = do
  s <- T.readFile fp
  case runExcept (runFileParser fp (moduleP fp) s) of
    Left err -> pure (Left err)
    Right prog -> pure (pure prog)

getTypecheckedDecls :: FilePath -> IO (Either (NonEmpty Error) TST.Module)
getTypecheckedDecls fp = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      fmap snd <$> (fst <$> inferProgramIO defaultDriverState decls)
    Left err -> return (Left err)

typeInferenceBenchmarks :: [FilePath] -> Benchmark
typeInferenceBenchmarks fps = bgroup "Type inference" (inferType <$> fps)

inferType :: FilePath -> Benchmark
inferType fp = bench ("Example: " <> fp) $ whnfIO (getTypecheckedDecls fp)

main :: IO ()
main = do
    examples <- getAvailableExamples
    defaultMain [typeInferenceBenchmarks examples]
