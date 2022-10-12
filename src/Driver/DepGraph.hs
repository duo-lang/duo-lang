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
import Data.Text (Text)
import Data.Text qualified as T
import Data.Maybe (fromJust)
import Data.List (intersperse)
import Control.Monad.Except
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree ( Gr )
import Data.Graph.Inductive.Query.BFS ( bft )
import Data.Graph.Inductive.Query.DFS (topsort')
import Data.GraphViz
import System.FilePath ( (</>), (<.>))
import System.Directory ( createDirectoryIfMissing, getCurrentDirectory )
import Data.Text.Lazy (pack)

import Pretty.Pretty ( ppPrint, ppPrintString )
import Driver.Definition ( DriverM, getModuleDeclarations, getSymbolTable )
import Resolution.SymbolTable
    ( SymbolTable(imports) )
import Syntax.CST.Names ( ModuleName(..) )
import Errors ( throwOtherError )
import Loc ( defaultLoc )

-- | A dependency Graph which represents the structure of imports.
data DepGraph = MkDepGraph { graph :: Gr ModuleName ()
                           , node_supply :: Int
                           , name_map :: Map ModuleName Node
                           , visited :: [ModuleName]
                           }

defaultDepGraph :: DepGraph
defaultDepGraph = MkDepGraph { graph = empty
                             , node_supply = 0
                             , name_map = M.empty
                             , visited = []
                             }

-- | Order in which modules should be compiled. (=Topological sorting of DepGraph)
type CompilationOrder = [ModuleName]

---------------------------------------------------------------------------------
-- Creating a dependency graph
---------------------------------------------------------------------------------

-- | Create the dependency graph by recursively following import statements.
createDepGraph :: ModuleName -> DriverM DepGraph
createDepGraph mn = createDepGraph' [mn] defaultDepGraph

lookupOrInsert :: DepGraph -> ModuleName -> (Node, DepGraph)
lookupOrInsert depGraph@MkDepGraph {..} mn = case M.lookup mn name_map of
  Nothing -> (node_supply, depGraph { graph = insNode (node_supply, mn) graph
                                    , node_supply = node_supply + 1
                                    , name_map = M.insert mn node_supply name_map })
  Just nd -> (nd, depGraph)

lookupOrInserts :: DepGraph -> [ModuleName] -> ([Node], DepGraph)
lookupOrInserts depGraph [] = ([],depGraph)
lookupOrInserts depGraph (mn:mns) =
  let 
    (nodes,depGraph') = lookupOrInserts depGraph mns
    (node, depGraph'') = lookupOrInsert depGraph' mn
  in
    (node:nodes,depGraph'')


createDepGraph' :: [ModuleName] -> DepGraph -> DriverM DepGraph
createDepGraph' [] depGraph = pure depGraph
createDepGraph' (mn:mns) depGraph | mn `elem` visited depGraph = createDepGraph' mns depGraph
                                  | otherwise = do
                                      -- We have to insert the current modulename
                                      let (this, depGraph') = lookupOrInsert depGraph mn
                                      decls <- getModuleDeclarations mn
                                      symTable <- getSymbolTable decls
                                      let importedModules :: [ModuleName] = fst <$> imports symTable
                                      -- We have to insert all the imported module names
                                      let (nodes, depGraph'') = lookupOrInserts depGraph' importedModules
                                      -- We have to insert the edges
                                      let newEdges :: [(Node, Node, ())] = [(this, imported, ()) | imported <- nodes]
                                      let depGraph''' = depGraph'' { graph = insEdges newEdges (graph depGraph''), visited = mn : visited depGraph''}
                                      createDepGraph' (importedModules ++ mns) depGraph'''


-- | Compute the transitive closure where the edges are annotated with a witnessing path.
tc :: Gr ModuleName () -> Gr ModuleName [Node]
tc g = newEdges `insEdges` insNodes ln empty
  where
    ln :: [LNode ModuleName]
    ln       = labNodes g
    newEdges :: [(Node, Node, [Node])]
    newEdges = [ (u, head path, path) | (u, u',_) <- labEdges g,  path <- bft u' g ]

-- | Return all the paths which witness that there is a path from `a` to `a`.
hasLoop ::  Gr ModuleName [Node] -> [[Node]]
hasLoop gr = map (\(_,_,e) -> e) (filter (\(x,y,_) -> x == y) (labEdges gr))

-- | Throws an error if the dependency graph contains a cycle of imports.
checkRecursiveImports :: DepGraph -> DriverM ()
checkRecursiveImports depgraph = case hasLoop (tc (graph depgraph)) of
    (x:_) -> throwOtherError defaultLoc [explainRecursiveLoop depgraph x]
    [] -> pure ()

explainRecursiveLoop :: DepGraph -> [Node] -> Text
explainRecursiveLoop gr nodes = "Recursive module imports are not allowed. Involved Modules: " <> T.concat (intersperse "," (ppPrint <$> lnodes))
  where
    lnodes :: [ModuleName]
    lnodes = fromJust <$> (lab (graph gr) <$> nodes)

-- | Return a compilation order for a given dependency graph.
-- Throws an error if the dependency graph is not acyclical.
topologicalSort :: DepGraph -> DriverM CompilationOrder
topologicalSort depGraph = do
    checkRecursiveImports depGraph
    pure $ reverse $ topsort' (graph depGraph)


---------------------------------------------------------------------------------
-- Prettyprinting Dependency Graphs
---------------------------------------------------------------------------------

depGraphToDot :: DepGraph -> DotGraph Node
depGraphToDot depgraph = graphToDot depGraphParams (graph depgraph)

depGraphParams :: GraphvizParams Node ModuleName () () ModuleName
depGraphParams = defaultParams
  { fmtNode = \(_,mn) ->
    [ style filled
    , fillColor Gray
    , textLabel ((pack . show) (mn_base mn))]
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
    putStrLn ("[" ++ show n ++ "] " ++ ppPrintString mn)
