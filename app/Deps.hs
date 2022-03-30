module Deps (runDeps) where

import Driver.Definition
import Driver.DepGraph
import Errors
import Pretty.Pretty

runDeps :: FilePath -> IO ()
runDeps fp = do
    res <- createDeps fp
    case res of
        Left err -> ppPrintIO err
        Right (depGraph, compilationOrder) -> do
            putStrLn "Dependency graph:"
            printDepGraph depGraph
            putStrLn "Compilation order:"
            printCompilationOrder compilationOrder

createDeps :: FilePath -> IO (Either Error (DepGraph,CompilationOrder))
createDeps fp = fmap fst <$> execDriverM (DriverState defaultInferenceOptions mempty) (createDeps' fp)

createDeps' :: FilePath -> DriverM (DepGraph, CompilationOrder)
createDeps' fp = do
    depGraph <- createDepGraph fp
    compilationOrder <- topologicalSort depGraph
    pure (depGraph, compilationOrder)