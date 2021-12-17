module TypeAutomata.Simplify where

import Control.Monad.Except
import Data.GraphViz
    ( isGraphvizInstalled, runGraphviz, GraphvizOutput(XDot, Jpeg) )
import System.FilePath ( (</>), (<.>))
import System.Directory ( createDirectoryIfMissing, getCurrentDirectory )

import Errors ( Error(..), throwOtherError )    
import Pretty.TypeAutomata (typeAutToDot)
import Syntax.Types
import Syntax.Kinds
import TypeAutomata.Definition
import TypeAutomata.ToAutomaton ( typeToAut )
import TypeAutomata.FromAutomaton ( autToType )
import TypeAutomata.RemoveEpsilon ( removeEpsilonEdges )
import TypeAutomata.Determinize (determinize)
import TypeAutomata.RemoveAdmissible ( removeAdmissableFlowEdges )
import TypeAutomata.Minimize ( minimize )
import TypeAutomata.Lint ( lint )
import Utils (allEq)

------------------------------------------------------------------------------
-- Printing TypeAutomata
------------------------------------------------------------------------------

printGraph :: MonadIO m => Bool -> String -> TypeAut' EdgeLabelNormal f pol -> m ()
printGraph False _ _ = pure ()
printGraph True fileName aut = liftIO $ do
  let graphDir = "graphs"
  let fileUri = "  file://"
  let jpg = "jpg"
  let xdot = "xdot"
  dotInstalled <- isGraphvizInstalled
  if dotInstalled
    then do
      createDirectoryIfMissing True graphDir
      currentDir <- getCurrentDirectory
      _ <- runGraphviz (typeAutToDot aut) Jpeg           (graphDir </> fileName <.> jpg)
      _ <- runGraphviz (typeAutToDot aut) (XDot Nothing) (graphDir </> fileName <.> xdot)
      putStrLn (fileUri ++ currentDir </> graphDir </> fileName <.> jpg)
    else do
      putStrLn "Cannot generate graphs: graphviz executable not found in path."

------------------------------------------------------------------------------
-- Printing TypeAutomata
------------------------------------------------------------------------------

simplify :: (MonadIO m, MonadError Error m)
         => TypeScheme pol
         -> Bool -- ^ Whether to print Graphs
         -> String -- ^ Name of the declaration
         -> m (TypeScheme pol)
simplify tys print str = do
    -- Check that input type is kind correct
    kindCheckTypeScheme tys
    -- Read typescheme into automaton
    typeAut <- liftEither $ typeToAut tys
    lint typeAut
    -- Remove epsilon edges
    let typeAutDet = removeEpsilonEdges typeAut
    lint typeAutDet
    printGraph print ("0_typeAut" <> "_" <> str) typeAutDet
    -- Determinize the automaton
    let typeAutDet' = determinize typeAutDet
    lint typeAutDet'
    printGraph print ("1_typeAutDet" <> "_"  <> str) typeAutDet'
    -- Remove admissable flow edges
    let typeAutDetAdms = removeAdmissableFlowEdges typeAutDet'
    lint typeAutDetAdms
    printGraph print ("2_typeAutDetAdms" <> "_"  <> str) typeAutDetAdms
    -- Minimize automaton
    let typeAutMin = minimize typeAutDetAdms
    lint typeAutMin
    printGraph print ("3_minTypeAut" <> "_"  <> str) typeAutMin
    -- Read back to type
    --tysSimplified <- autToType typeAutMin
    liftEither $ autToType typeAutMin
    

kindCheckTypeScheme :: MonadError Error m
                    => TypeScheme pol -> m ()
kindCheckTypeScheme (TypeScheme tvars monotype) = kindCheckType tvars monotype

kindCheckType :: MonadError Error m
              => [(TVar, Kind)] -> Typ pol -> m ()
kindCheckType _ (TyVar _ Nothing _) = throwOtherError ["KindCheck: Type variable not annotated."]
kindCheckType env (TyVar _ (Just kind) tv) = case lookup tv env of
    Nothing -> throwOtherError ["Foo"]
    Just kind' -> if kind == kind' then pure () else throwOtherError["KindCheck: Type variable is annotated with different kind from context."]
kindCheckType env (TyData _ _ xtors)   = sequence_ $ kindCheckXtors env <$> xtors
kindCheckType env (TyCodata _ _ xtors) = sequence_ $ kindCheckXtors env <$> xtors
kindCheckType _ (TyNominal _ Nothing _) = throwOtherError["KindCheck: TyNominal not annotated."]
kindCheckType _ (TyNominal _ (Just _) _) = pure ()
kindCheckType _ (TySet _ Nothing _) = throwOtherError["KindCheck: TySet not annotated."]
kindCheckType _ (TySet _ (Just kind) typs) = do
    let kinds = getKind <$> typs
    if allEq (kind:kinds)
        then pure ()
        else throwOtherError["KindCheck: TySet contains different kinds."]
kindCheckType env (TyRec _ tv ty) = kindCheckType ((tv, getKind ty) : env) ty
    
kindCheckPrdCnsType :: MonadError Error m
                    =>  [(TVar, Kind)] -> PrdCnsType pol -> m ()
kindCheckPrdCnsType env (PrdCnsType _ ty) = kindCheckType env ty

kindCheckXtors :: MonadError Error m 
               => [(TVar, Kind)] -> XtorSig pol -> m ()
kindCheckXtors env (MkXtorSig _ args) = sequence_ $ kindCheckPrdCnsType env <$> args

