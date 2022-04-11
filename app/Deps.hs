module Deps (runDeps) where

import Driver.Definition
import Driver.DepGraph
import Errors
import Pretty.Pretty
import Syntax.Common

runDeps :: ModuleName -> IO ()
runDeps mn = do
    res <- createDeps mn
    case res of
        Left err -> ppPrintIO err
        Right (depGraph, compilationOrder) -> do
            putStrLn "Dependency graph:"
            printDepGraph depGraph
            putStrLn "Compilation order:"
            printCompilationOrder compilationOrder

createDeps :: ModuleName -> IO (Either Error (DepGraph,CompilationOrder))
createDeps fp = fmap fst <$> execDriverM defaultDriverState (createDeps' fp)

createDeps' :: ModuleName -> DriverM (DepGraph, CompilationOrder)
createDeps' fp = do
    depGraph <- createDepGraph fp
    compilationOrder <- topologicalSort depGraph
    pure (depGraph, compilationOrder)