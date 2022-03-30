module Driver.DepGraph
  ( -- Types
    DepGraph
  , CompilationOrder
    -- Functions
  , createDepGraph
  , topologicalSort
  , printDepGraph
  , printCompilationOrder
  ) where

import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Control.Monad.Except
import Data.Graph.Inductive.Basic (hasLoop)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.TransClos (tc)
import Data.Graph.Inductive.Query.DFS (topsort')
import Data.GraphViz
import System.FilePath ( (</>), (<.>))
import System.Directory ( createDirectoryIfMissing, getCurrentDirectory )
import Data.GraphViz
    ( isGraphvizInstalled, runGraphviz, GraphvizOutput(XDot, Jpeg) )
import Data.Text.Lazy (pack)

import Parser.Definition
import Parser.Program
import Pretty.Pretty
import Driver.Definition
import Renamer.SymbolTable
import Syntax.Common
import Errors
import Utils

-- | A dependency Graph which represents the structure of imports.
type DepGraph = Gr ModuleName ()

-- | Order in which modules should be compiled. (=Topological sorting of DepGraph)
type CompilationOrder = [ModuleName]

---------------------------------------------------------------------------------
-- Creating a dependency graph
---------------------------------------------------------------------------------

-- | Create the dependency graph by recursively following import statements.
createDepGraph :: FilePath -> DriverM DepGraph
createDepGraph fp = createDepGraph' [MkModuleName (T.pack fp)] [] empty defaultModuleNameMap

type ModuleNameMap = (Int, Map ModuleName Node)

defaultModuleNameMap :: ModuleNameMap
defaultModuleNameMap = (0, M.empty)

lookupModule :: ModuleNameMap -> ModuleName -> (Node, ModuleNameMap)
lookupModule (counter,map) mn = case M.lookup mn map of
  Nothing -> (counter, (counter + 1, M.insert mn counter map))
  Just nd -> (nd     , (counter    ,                     map))

lookupModules :: ModuleNameMap -> [ModuleName] -> ([Node], ModuleNameMap)
lookupModules mnm [] = ([],mnm)
lookupModules mnm (mn:mns) =
  let 
    (nodes,mnm') = lookupModules mnm mns
    (node, mnm'') = lookupModule mnm' mn
  in
    (node:nodes,mnm'')


createDepGraph' :: [ModuleName] -> [ModuleName] -> DepGraph -> ModuleNameMap -> DriverM DepGraph
createDepGraph' [] _cache depGraph _mnm = pure depGraph
createDepGraph' (mn:mns) cache depGraph mnm | mn `elem` cache = createDepGraph' mns cache depGraph mnm
                                            | otherwise = do
                                                fp <- findModule mn defaultLoc
                                                file <- liftIO $ T.readFile fp
                                                decls <- runFileParser fp programP file
                                                let importedModules = imports (createSymbolTable decls)
                                                let (nodes, mnm') = lookupModules mnm (mn:(fst <$> importedModules))
                                                let newNodes :: [(Node, ModuleName)] = zip nodes (mn:(fst <$> importedModules))
                                                let depGraph' = insNodes newNodes depGraph
                                                let newEdges :: [(Node, Node, ())] = [(head nodes, nd, ()) | nd <- tail nodes]
                                                let depGraph'' = insEdges newEdges depGraph'
                                                createDepGraph' ((fst <$> importedModules) ++ mns) (mn:cache) depGraph'' mnm'




-- | Throws an error if the dependency graph contains a cycle of imports.
checkRecursiveImports :: DepGraph -> DriverM ()
checkRecursiveImports depgraph = case hasLoop (tc depgraph) of
    True -> throwError (OtherError Nothing "Imports contain a loop")
    False -> pure ()

-- | Return a compilation order for a given dependency graph.
-- Throws an error if the dependency graph is not acyclical.
topologicalSort :: DepGraph -> DriverM CompilationOrder
topologicalSort depGraph = do
    checkRecursiveImports depGraph
    pure $ reverse $ topsort' depGraph


---------------------------------------------------------------------------------
-- Prettyprinting Dependency Graphs
---------------------------------------------------------------------------------

depGraphToDot :: DepGraph -> DotGraph Node
depGraphToDot depgraph = graphToDot depGraphParams depgraph

depGraphParams :: GraphvizParams Node ModuleName () () ModuleName
depGraphParams = defaultParams
  { fmtNode = \(_,mn) ->
    [ style filled
    , fillColor Gray
    , textLabel ((pack . show) (unModuleName mn))]
  }

printDepGraph :: MonadIO m => DepGraph -> m ()
printDepGraph depGraph = liftIO $ do
    let fileName = "deps"
    let graphDir = "graphs"
    let fileUri = "  file://"
    let jpg = "jpg"
    let xdot = "xdot"
    dotInstalled <- isGraphvizInstalled
    if dotInstalled
        then do
          createDirectoryIfMissing True graphDir
          let depGraphDot = depGraphToDot depGraph
          _ <- runGraphviz depGraphDot Jpeg (graphDir </> fileName <.> jpg)
          _ <- runGraphviz depGraphDot (XDot Nothing) (graphDir </> fileName <.> xdot)
          currentDir <- getCurrentDirectory
          putStrLn (fileUri ++ currentDir </> graphDir </> fileName <.> jpg)
        else do
          putStrLn "Cannot generate graphs: graphviz executable not found in path."

---------------------------------------------------------------------------------
-- Prettyprinting Compilation Order
---------------------------------------------------------------------------------

printCompilationOrder :: MonadIO m => CompilationOrder -> m ()
printCompilationOrder compilationOrder = liftIO $ do
  forM_ (zip [(1 :: Int)..] compilationOrder) $ \(n,mn) -> do
    putStrLn ("[" ++ show n ++ "] " ++ (ppPrintString mn))
