module TypeAutomata.Simplify where

import Control.Monad.Except
import System.FilePath ( (</>), (<.>))
import System.Directory ( createDirectoryIfMissing, getCurrentDirectory )
import Data.GraphViz
    ( isGraphvizInstalled, runGraphviz, GraphvizOutput(XDot, Jpeg) )
import Data.Map qualified as M
import Pretty.TypeAutomata (typeAutToDot)

import Errors ( Error )
import Syntax.CommonTerm
import Syntax.Types
import Syntax.Zonking
import TypeAutomata.Definition
import TypeAutomata.ToAutomaton ( typeToAut )
import TypeAutomata.FromAutomaton ( autToType )
import TypeAutomata.RemoveEpsilon ( removeEpsilonEdges )
import TypeAutomata.Determinize (determinize)
import TypeAutomata.RemoveAdmissible ( removeAdmissableFlowEdges )
import TypeAutomata.Minimize ( minimize )
import TypeAutomata.Lint ( lint )
import TypeInference.Constraints

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
    liftEither $ autToType typeAutMin

------------------------------------------------------------------------------
-- Compute a Bisubstitution from a SolverResult
------------------------------------------------------------------------------

-- | Create a type `< '$BS(u1,...,un)[u1,...,un] >` from the unification variables
-- of the domain of the SolverResult.
createBSType :: SolverResult -> Typ Pos
createBSType MkSolverResult { tvarSolution } = TyData PosRep Nothing [bs_xtor]
  where
    bs_xtor = MkXtorSig (MkXtorName Structural "$BS") (prdArgs ++ cnsArgs)
    prdArgs = (\tv -> PrdCnsType PrdRep (TyVar PosRep Nothing tv)) <$> M.keys tvarSolution
    cnsArgs = (\tv -> PrdCnsType CnsRep (TyVar NegRep Nothing tv)) <$> M.keys tvarSolution

-- | Takes a type `< '$BS(u1,...,un)[u1,...,un] >`, which was constructed using
-- the `createBSType` function, simplified using the typeautomata, and turns it into
-- a Bisubstitution.
readBisubstitution :: SolverResult -> Typ Pos -> Bisubstitution
readBisubstitution sr (TyData PosRep _ [MkXtorSig (MkXtorName Structural "$BS") args ]) =
  MkBisubstitution (readBisubstitution' (M.keys $ tvarSolution sr) args) (kvarSolution sr)
readBisubstitution _ ty = error ("readBisubstitution: Unexpected type: " <> show ty)

readBisubstitution' :: [TVar] -> LinearContext Pos -> M.Map TVar (Typ Pos, Typ Neg)
readBisubstitution' tvars ctxt = M.fromList (zipWith3 (\v p n -> (v, (p,n))) tvars (concatMap posF ctxt) (concatMap negF ctxt))
  where
    posF :: PrdCnsType Pos -> [Typ Pos]
    posF (PrdCnsType PrdRep ty) = [ty]
    posF _ = []

    negF :: PrdCnsType Pos -> [Typ Neg]
    negF (PrdCnsType CnsRep ty) = [ty]
    negF _ = []

computeBisubstitution :: (MonadIO m, MonadError Error m)
                      => SolverResult
                      -> m (Bisubstitution)
computeBisubstitution sr = do
  let ty = createBSType sr
  ty' <- undefined sr ty
  return $ readBisubstitution sr ty'