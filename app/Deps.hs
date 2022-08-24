module Deps (runDeps) where

import Data.List.NonEmpty ( NonEmpty )
import Driver.Definition
import Driver.DepGraph
import Errors
import Pretty.Errors (printLocatedReport)
import Syntax.CST.Names


runDeps :: ModuleName -> IO ()
runDeps mn = do
    res <- createDeps mn
    case res of
        Left errs -> mapM_ printLocatedReport errs
        Right (depGraph, compilationOrder) -> do
            putStrLn "Dependency graph:"
            printDepGraph depGraph
            putStrLn "Compilation order:"
            printCompilationOrder compilationOrder

createDeps :: ModuleName -> IO (Either (NonEmpty Error) (DepGraph,CompilationOrder))
createDeps fp =  do 
    (res, _) <-  execDriverM defaultDriverState (createDeps' fp) -- ignore warnings
    return (fst <$> res)

createDeps' :: ModuleName -> DriverM (DepGraph, CompilationOrder)
createDeps' fp = do
    depGraph <- createDepGraph fp
    compilationOrder <- topologicalSort depGraph
    pure (depGraph, compilationOrder)