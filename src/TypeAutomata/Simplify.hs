module TypeAutomata.Simplify where

import Control.Monad.Except
import System.FilePath ( (</>), (<.>))
import System.Directory ( createDirectoryIfMissing, getCurrentDirectory )
import Data.GraphViz
    ( isGraphvizInstalled, runGraphviz, GraphvizOutput(XDot, Jpeg) )
import Data.List.NonEmpty (NonEmpty)
import Pretty.TypeAutomata (typeAutToDot)

import Errors ( Error )    
import Syntax.RST.Types ( TypeScheme )
import TypeAutomata.Definition
import TypeAutomata.ToAutomaton ( typeToAut )
import TypeAutomata.FromAutomaton ( autToType )
import TypeAutomata.RemoveEpsilon ( removeEpsilonEdges )
import TypeAutomata.Determinize (determinize)
import TypeAutomata.RemoveAdmissible ( removeAdmissableFlowEdges )
import TypeAutomata.Minimize ( minimize )
import TypeAutomata.Lint ( lint )

------------------------------------------------------------------------------
-- Printing TypeAutomata
------------------------------------------------------------------------------

printGraph :: MonadIO m => Bool -> Bool -> String -> TypeAut' EdgeLabelNormal f pol -> m ()
printGraph False _ _ _ = pure ()
printGraph True showId fileName aut = liftIO $ do
  let graphDir = "graphs"
  let fileUri = "  file://"
  let jpg = "jpg"
  let xdot = "xdot"
  dotInstalled <- isGraphvizInstalled
  if dotInstalled
    then do
      createDirectoryIfMissing True graphDir
      currentDir <- getCurrentDirectory
      _ <- runGraphviz (typeAutToDot showId aut) Jpeg           (graphDir </> fileName <.> jpg)
      _ <- runGraphviz (typeAutToDot showId aut) (XDot Nothing) (graphDir </> fileName <.> xdot)
      putStrLn (fileUri ++ currentDir </> graphDir </> fileName <.> jpg)
    else do
      putStrLn "Cannot generate graphs: graphviz executable not found in path."

------------------------------------------------------------------------------
-- Printing TypeAutomata
------------------------------------------------------------------------------

simplify :: (MonadIO m, MonadError (NonEmpty Error) m)
         => TypeScheme pol
         -> Bool -- ^ Whether to print Graphs
         -> String -- ^ Name of the declaration
         -> m (TypeScheme pol)
simplify tys print str = do
    -- Read typescheme into automaton
    typeAut <- liftEither $ typeToAut tys
    lint typeAut
    -- Remove epsilon edges
    let typeAutDet = removeEpsilonEdges typeAut
    lint typeAutDet
    printGraph print False ("0_typeAut" <> "_" <> str) typeAutDet
    -- Determinize the automaton
    let typeAutDet' = determinize typeAutDet
    lint typeAutDet'
    printGraph print False ("1_typeAutDet" <> "_"  <> str) typeAutDet'
    -- Remove admissable flow edges
    let typeAutDetAdms = removeAdmissableFlowEdges typeAutDet'
    lint typeAutDetAdms
    printGraph print False ("2_typeAutDetAdms" <> "_"  <> str) typeAutDetAdms
    -- Minimize automaton
    let typeAutMin = minimize typeAutDetAdms
    lint typeAutMin
    printGraph print False ("3_minTypeAut" <> "_"  <> str) typeAutMin
    -- Read back to type
    liftEither $ autToType typeAutMin
