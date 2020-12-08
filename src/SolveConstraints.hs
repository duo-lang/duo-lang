module SolveConstraints
  ( solveConstraints
  , removeEpsilonEdges
  , removeIslands
  ) where

import Data.Graph.Inductive.Graph

import Control.Monad.State
import Control.Monad.Except
import Data.Ord (comparing)
import Data.List (sortBy, (\\))
import qualified Data.Set as S

import Syntax.Types
import Syntax.TypeGraph
import Syntax.Terms
import Utils
import Pretty
import TypeAutomata.Determinize (removeEpsilonEdges, removeIslands)

data SolverState = SolverState
  { sst_gr :: TypeGrEps
  , sst_cache :: [Constraint] }

type SolverM a = (StateT SolverState (Except String)) a

runSolverM :: SolverM a -> SolverState -> Either String (a, SolverState)
runSolverM m initSt = runExcept (runStateT m initSt)

uvarToNodeId :: UVar -> PrdCns -> Node
uvarToNodeId uv Prd = 2 * uvar_id uv
uvarToNodeId uv Cns  = 2 * uvar_id uv + 1

nodeIdToUVar :: Node -> UVar
nodeIdToUVar n = MkUVar (n `div` 2)

typeToHeadCons :: SimpleType -> HeadCons
typeToHeadCons (TyVar _) = emptyHeadCons
typeToHeadCons (SimpleType s xtors) = singleHeadCons s (S.fromList (map sig_name xtors))

modifyGraph :: (TypeGrEps -> TypeGrEps) -> SolverM ()
modifyGraph f = modify (\(SolverState gr cache) -> SolverState (f gr) cache)

modifyCache :: ([Constraint] -> [Constraint]) -> SolverM ()
modifyCache f = modify (\(SolverState gr cache) -> SolverState gr (f cache))

typeToGraph :: PrdCns -> SimpleType -> SolverM Node
typeToGraph pol (TyVar uv) = return (uvarToNodeId uv pol)
typeToGraph pol (SimpleType s xtors) = do
  newNodeId <- head . newNodes 1 . sst_gr <$> get
  let hc = typeToHeadCons (SimpleType s xtors)
  modifyGraph (insNode (newNodeId, (pol, hc)))
  _ <- forM xtors $ \(MkXtorSig xt (Twice prdTypes cnsTypes)) -> do
    let (n,m) = (length prdTypes, length cnsTypes)
    _ <- forM [0..n-1] $ \i -> do
      prdNode <- typeToGraph (applyVariance s Prd pol) (prdTypes !! i)
      modifyGraph (insEdge (newNodeId, prdNode, Just (EdgeSymbol s xt Prd i)))
    _ <- forM [0..m-1] $ \j -> do
      cnsNode <- typeToGraph (applyVariance s Cns pol) (cnsTypes !! j)
      modifyGraph (insEdge (newNodeId, cnsNode, Just (EdgeSymbol s xt Cns j)))
    return ()
  return newNodeId

graphToType :: Node -> SolverM SimpleType
graphToType i = do
  gr <- sst_gr <$> get
  case lab gr i of
    Just (_,HeadCons Nothing Nothing) -> return (TyVar (nodeIdToUVar i))
    Just (_,HeadCons (Just xtors) Nothing) ->
      SimpleType Data <$> (forM (S.toList xtors) $ \xt -> do
        let prdNodes = map fst $ sortBy (comparing snd) [(nd,j) | (_,nd,Just (EdgeSymbol Data xt' Prd j)) <- out gr i, xt == xt']
        prdTypes <- mapM graphToType prdNodes
        let cnsNodes = map fst $ sortBy (comparing snd) [(nd,j) | (_,nd,Just (EdgeSymbol Data xt' Cns j)) <- out gr i, xt == xt']
        cnsTypes <- mapM graphToType cnsNodes
        return $ (MkXtorSig xt (Twice prdTypes cnsTypes)))
    Just (_,HeadCons Nothing (Just xtors)) -> do
      SimpleType Codata <$> (forM (S.toList xtors) $ \xt -> do
        let prdNodes = map fst $ sortBy (comparing snd) [(nd,j) | (_,nd,Just (EdgeSymbol Codata xt' Prd j)) <- out gr i, xt == xt']
        prdTypes <- mapM graphToType prdNodes
        let cnsNodes = map fst $ sortBy (comparing snd) [(nd,j) | (_,nd,Just (EdgeSymbol Codata xt' Cns j)) <- out gr i, xt == xt']
        cnsTypes <- mapM graphToType cnsNodes
        return (MkXtorSig xt (Twice prdTypes cnsTypes)))
    Nothing -> throwError "graphToType: node doesn't exist in graph"

subConstraints :: Constraint -> SolverM [Constraint]
subConstraints cs@(SubType (SimpleType Data xtors1) (SimpleType Data xtors2))
  = if not . null $ (map sig_name xtors1) \\ (map sig_name xtors2)
    then throwError $ "Constraint: \n      " ++ ppPrint cs ++ "\nis unsolvable, because xtor \"" ++
                      ppPrint (head $ (map sig_name xtors1) \\ (map sig_name xtors2)) ++
                      "\" occurs only in the left side."
    else return $ do -- list monad
      (MkXtorSig xtName (Twice prd1 cns1)) <- xtors1
      let Just (Twice prd2 cns2) = lookup xtName ((\(MkXtorSig xt args) -> (xt, args)) <$> xtors2) --safe, because of check above
      zipWith SubType prd1 prd2 ++ zipWith SubType cns2 cns1
subConstraints cs@(SubType (SimpleType Codata xtors1) (SimpleType Codata xtors2))
  = if not . null $ (map sig_name xtors2) \\ (map sig_name xtors1)
    then throwError $ "Constraint: \n      " ++ ppPrint cs ++ "\nis unsolvable, because xtor \"" ++
                      ppPrint (head $ (map sig_name xtors2) \\ (map sig_name xtors1)) ++
                      "\" occurs only in the right side."
    else return $ do -- list monad
      (MkXtorSig xtName (Twice prd2 cns2)) <- xtors2
      let Just (Twice prd1 cns1) = lookup xtName ((\(MkXtorSig xt args) -> (xt, args)) <$> xtors1) --safe, because of check above
      zipWith SubType prd2 prd1 ++ zipWith SubType cns1 cns2
subConstraints cs@(SubType (SimpleType Data _) (SimpleType Codata _))
  = throwError $ "Constraint: \n      " ++ ppPrint cs ++ "\n is unsolvable. A data type can't be a subtype of a codata type!"
subConstraints cs@(SubType (SimpleType Codata _) (SimpleType Data _))
  = throwError $ "Constraint: \n      " ++ ppPrint cs ++ "\n is unsolvable. A codata type can't be a subtype of a data type!"
subConstraints _ = return [] -- constraint is atomic

epsilonSuccs :: TypeGrEps -> Node -> [Node]
epsilonSuccs gr i = [j | (_,j,Nothing) <- out gr i]

solve :: [Constraint] -> SolverM ()
solve [] = return ()
solve (cs:css) = do
  SolverState gr cache <- get
  if cs `elem` cache
    then solve css
    else do
      modifyCache (cs:)
      case cs of
        (SubType (TyVar uv1) (TyVar uv2)) -> do
          let (uv1Cns, uv1Prd) = (uvarToNodeId uv1 Cns, uvarToNodeId uv1 Prd)
          let (uv2Cns, uv2Prd) = (uvarToNodeId uv2 Cns, uvarToNodeId uv2 Prd)
          lbs <- mapM graphToType (epsilonSuccs gr uv1Prd)
          ubs <- mapM graphToType (epsilonSuccs gr uv2Cns)
          modifyGraph (insEdge (uv2Prd,uv1Prd,Nothing))
          modifyGraph (insEdge (uv1Cns,uv2Cns,Nothing))
          let newCss = [SubType lb ub | lb <- lbs, ub <- ubs]
          solve (newCss ++ css)
        (SubType (TyVar uv) ub) -> do
          let (uvCns, uvPrd) = (uvarToNodeId uv Cns, uvarToNodeId uv Prd)
          ubNode <- typeToGraph Cns ub
          modifyGraph (insEdge (uvCns,ubNode,Nothing))
          lbs <- mapM graphToType (epsilonSuccs gr uvPrd)
          let newCss = [SubType lb ub | lb <- lbs]
          solve (newCss ++ css)
        (SubType lb (TyVar uv)) -> do
          let (uvCns, uvPrd) = (uvarToNodeId uv Cns, uvarToNodeId uv Prd)
          lbNode <- typeToGraph Prd lb
          modifyGraph (insEdge (uvPrd,lbNode,Nothing))
          ubs <- mapM graphToType (epsilonSuccs gr uvCns)
          let newCss = [SubType lb ub | ub <- ubs]
          solve (newCss ++ css)
        _ -> do
          subCss <- subConstraints cs
          solve (subCss ++ css)

-- PrdCns argument is needed to determine polarity of start state:
-- Prd means positive start state, Cns means negative start state
solveConstraints :: [Constraint] -> [UVar] -> SimpleType -> PrdCns -> Either Error TypeAut
solveConstraints css uvs ty pc =
  let
    uvNodes = [(uvarToNodeId uv pol, (pol, emptyHeadCons)) | uv <- uvs, pol <- [Prd,Cns]]
    flowEdges = [(uvarToNodeId uv Cns, uvarToNodeId uv Prd) | uv <- uvs]
    startPol = pc
    initState0 = SolverState
      { sst_gr = mkGraph uvNodes []
      , sst_cache = [] }
    -- initializes the graph with the given simple type
    Right (start, initState1) = runSolverM (typeToGraph startPol ty) initState0
  in
    case runSolverM (solve css) initState1 of
      Left err -> Left (SolveConstraintsError err)
      Right (_,SolverState gr _) ->
        let
          aut = TypeAut { ta_gr = gr, ta_starts = [start], ta_flowEdges = flowEdges }
        in
          Right $ (removeIslands . removeEpsilonEdges) aut

