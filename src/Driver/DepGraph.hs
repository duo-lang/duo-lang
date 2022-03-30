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

import Data.Text qualified as T
import Data.Text.IO qualified as T
import Control.Monad.Except
import Data.Graph.Inductive.Basic (hasLoop)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Graph.Inductive.Query.TransClos (tc)
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
import Syntax.Common
import Errors
import Utils

-- | A dependency Graph which represents the structure of imports.
type DepGraph = Gr ModuleName ()

-- | Order in which modules should be compiled. (=Topological sorting of DepGraph)
type CompilationOrder = [ModuleName]

-- | Create the dependency graph by recursively following import statements.
createDepGraph :: FilePath -> DriverM DepGraph
createDepGraph fp = createDepGraph' [MkModuleName (T.pack fp)] [] empty

createDepGraph' :: [ModuleName] -> [ModuleName] -> DepGraph -> DriverM DepGraph
createDepGraph' [] _cache depGraph = pure depGraph
createDepGraph' (mn:mns) cache depGraph | mn `elem` cache = createDepGraph' mns cache depGraph
                                        | otherwise = do
                                          fp <- findModule mn defaultLoc
                                          file <- liftIO $ T.readFile fp
                                          decls <- runFileParser fp programP file
                                          undefined



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
    pure []


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
