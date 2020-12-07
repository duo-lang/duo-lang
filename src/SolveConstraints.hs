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
  { sst_gr :: TypeAutEps
  , sst_cache :: [Constraint] }

type SolverM a = (StateT SolverState (Except Error)) a

runSolverM :: SolverM a -> SolverState -> Either Error (a, SolverState)
runSolverM m initSt = runExcept (runStateT m initSt)

throwSolverError :: String -> SolverM a
throwSolverError = throwError . SolveConstraintsError

uvarToNodeId :: UVar -> Polarity -> Node
uvarToNodeId uv Pos = 2 * uvar_id uv
uvarToNodeId uv Neg  = 2 * uvar_id uv + 1

nodeIdToUVar :: Node -> UVar
nodeIdToUVar n = MkUVar (n `div` 2)

typeToHeadCons :: SimpleType -> HeadCons
typeToHeadCons (TyVar _) = emptyHeadCons
typeToHeadCons (SimpleType s xtors) = singleHeadCons s (S.fromList (map sig_name xtors))

modifyGraph :: (TypeGrEps -> TypeGrEps) -> SolverM ()
modifyGraph f = modify (\(SolverState aut@TypeAut { ta_gr } cache) -> SolverState aut { ta_gr = f ta_gr } cache)

modifyCache :: ([Constraint] -> [Constraint]) -> SolverM ()
modifyCache f = modify (\(SolverState gr cache) -> SolverState gr (f cache))

typeToGraph :: Polarity -> SimpleType -> SolverM Node
typeToGraph pol (TyVar uv) = return (uvarToNodeId uv pol)
typeToGraph pol (SimpleType s xtors) = do
  newNodeId <- gets (head . newNodes 1 . ta_gr . sst_gr)
  let hc = typeToHeadCons (SimpleType s xtors)
  modifyGraph (insNode (newNodeId, (pol, hc)))
  forM_ xtors $ \(MkXtorSig xt (Twice prdTypes cnsTypes)) -> do
    forM_ (enumerate prdTypes) $ \(i, prdType) -> do
      prdNode <- typeToGraph (applyVariance s Prd pol) prdType
      modifyGraph (insEdge (newNodeId, prdNode, Just (EdgeSymbol s xt Prd i)))
    forM_ (enumerate cnsTypes) $ \(j, cnsType) -> do
      cnsNode <- typeToGraph (applyVariance s Cns pol) cnsType
      modifyGraph (insEdge (newNodeId, cnsNode, Just (EdgeSymbol s xt Cns j)))
  return newNodeId

getNodeLabel :: Node -> SolverM NodeLabel
getNodeLabel i = do
  gr <- gets (ta_gr . sst_gr)
  case lab gr i of
    Just x -> return x
    Nothing -> throwSolverError ("getNodeLabel: node " ++ show i ++ " doesn't exist in graph.")

-- | At the given node 'i', get all outgoing Edges which are annotated with the XtorName 'xt' and reconstruct the corresponding xtorSig.
getXtorSig :: Node -> DataCodata -> XtorName -> SolverM (XtorSig SimpleType)
getXtorSig i dc xt = do
  gr <- gets (ta_gr . sst_gr)
  let outs = out gr i
  let prdNodes = map fst $ sortBy (comparing snd) [(nd,j) | (_,nd,Just (EdgeSymbol dc' xt' Prd j)) <- outs, xt == xt', dc == dc']
  prdTypes <- mapM graphToType prdNodes
  let cnsNodes = map fst $ sortBy (comparing snd) [(nd,j) | (_,nd,Just (EdgeSymbol dc' xt' Cns j)) <- outs, xt == xt', dc == dc']
  cnsTypes <- mapM graphToType cnsNodes
  return (MkXtorSig xt (Twice prdTypes cnsTypes))

graphToType :: Node -> SolverM SimpleType
graphToType i = do
  (_,hc) <- getNodeLabel i
  case hc of
    (HeadCons Nothing Nothing) -> return (TyVar (nodeIdToUVar i))
    (HeadCons (Just xtors) Nothing) -> do
      xtorSigs <- forM (S.toList xtors) $ \xt -> getXtorSig i Data xt
      return (SimpleType Data xtorSigs)
    (HeadCons Nothing (Just xtors)) -> do
      xtorSigs <- forM (S.toList xtors) $ \xt -> getXtorSig i Codata xt
      return (SimpleType Codata xtorSigs)
    (HeadCons (Just _) (Just _)) -> throwSolverError "Encountered HeadCons with both constructors and destructors during solving: Should not occur"

subConstraints :: Constraint -> SolverM [Constraint]
subConstraints cs@(SubType (SimpleType Data xtors1) (SimpleType Data xtors2))
  = if not . null $ (map sig_name xtors1) \\ (map sig_name xtors2)
    then throwSolverError $ unlines [ "Constraint:"
                                    , ppPrint cs
                                    , "is unsolvable, because xtor:"
                                    , ppPrint (head $ (map sig_name xtors1) \\ (map sig_name xtors2))
                                    , "occurs only in the left side." ]
    else return $ do -- list monad
      (MkXtorSig xtName (Twice prd1 cns1)) <- xtors1
      let Just (Twice prd2 cns2) = lookup xtName ((\(MkXtorSig xt args) -> (xt, args)) <$> xtors2) --safe, because of check above
      zipWith SubType prd1 prd2 ++ zipWith SubType cns2 cns1
subConstraints cs@(SubType (SimpleType Codata xtors1) (SimpleType Codata xtors2))
  = if not . null $ (map sig_name xtors2) \\ (map sig_name xtors1)
    then throwSolverError $ unlines [ "Constraint:"
                                    , ppPrint cs
                                    , "is unsolvable, because xtor:"
                                    , ppPrint (head $ (map sig_name xtors2) \\ (map sig_name xtors1))
                                    , "occurs only in the left side." ]
    else return $ do -- list monad
      (MkXtorSig xtName (Twice prd2 cns2)) <- xtors2
      let Just (Twice prd1 cns1) = lookup xtName ((\(MkXtorSig xt args) -> (xt, args)) <$> xtors1) --safe, because of check above
      zipWith SubType prd2 prd1 ++ zipWith SubType cns1 cns2
subConstraints cs@(SubType (SimpleType Data _) (SimpleType Codata _))
  = throwSolverError $  "Constraint: \n      " ++ ppPrint cs ++ "\n is unsolvable. A data type can't be a subtype of a codata type!"
subConstraints cs@(SubType (SimpleType Codata _) (SimpleType Data _))
  = throwSolverError $ "Constraint: \n      " ++ ppPrint cs ++ "\n is unsolvable. A codata type can't be a subtype of a data type!"
subConstraints _ = return [] -- constraint is atomic

epsilonSuccs :: TypeGrEps -> Node -> [Node]
epsilonSuccs gr i = [j | (_,j,Nothing) <- out gr i]

solve :: [Constraint] -> SolverM ()
solve [] = return ()
solve (cs:css) = do
  SolverState (TypeAut {ta_gr = gr}) cache <- get
  if cs `elem` cache
    then solve css
    else do
      modifyCache (cs:)
      case cs of
        (SubType (TyVar uv1) (TyVar uv2)) -> do
          let (uv1Neg, uv1Pos) = (uvarToNodeId uv1 Neg, uvarToNodeId uv1 Pos)
          let (uv2Neg, uv2Pos) = (uvarToNodeId uv2 Neg, uvarToNodeId uv2 Pos)
          lbs <- mapM graphToType (epsilonSuccs gr uv1Pos)
          ubs <- mapM graphToType (epsilonSuccs gr uv2Neg)
          modifyGraph (insEdge (uv2Pos,uv1Pos,Nothing))
          modifyGraph (insEdge (uv1Neg,uv2Neg,Nothing))
          let newCss = [SubType lb ub | lb <- lbs, ub <- ubs]
          solve (newCss ++ css)
        (SubType (TyVar uv) ub) -> do
          let (uvNeg, uvPos) = (uvarToNodeId uv Neg, uvarToNodeId uv Pos)
          ubNode <- typeToGraph Neg ub
          modifyGraph (insEdge (uvNeg,ubNode,Nothing))
          lbs <- mapM graphToType (epsilonSuccs gr uvPos)
          let newCss = [SubType lb ub | lb <- lbs]
          solve (newCss ++ css)
        (SubType lb (TyVar uv)) -> do
          let (uvNeg, uvPos) = (uvarToNodeId uv Neg, uvarToNodeId uv Pos)
          lbNode <- typeToGraph Pos lb
          modifyGraph (insEdge (uvPos,lbNode,Nothing))
          ubs <- mapM graphToType (epsilonSuccs gr uvNeg)
          let newCss = [SubType lb ub | ub <- ubs]
          solve (newCss ++ css)
        _ -> do
          subCss <- subConstraints cs
          solve (subCss ++ css)

-- | Creates an initial type automaton from a list of UVars.
mkInitialTypeAut :: [UVar] -> TypeAutEps
mkInitialTypeAut uvs =
  let
    uvNodes = [(uvarToNodeId uv pol, (pol, emptyHeadCons)) | uv <- uvs, pol <- [Pos,Neg]]
    flowEdges = [(uvarToNodeId uv Neg, uvarToNodeId uv Pos) | uv <- uvs]
  in
    TypeAut { ta_gr = mkGraph uvNodes []
            , ta_starts = []
            , ta_flowEdges = flowEdges
            }

-- | Creates the typeautomaton that results from solving constraints.
solveConstraintsOne :: [Constraint] -> [UVar] -> Either Error TypeAutEps
solveConstraintsOne css uvs = do
  let initState = SolverState { sst_gr = mkInitialTypeAut uvs, sst_cache = [] }
  (_, SolverState aut _) <- runSolverM (solve css) initState
  return aut

-- | Takes a given type automaton without a starting state, and adds a simple type as starting state to the automaton.
solveConstraintsTwo :: TypeAutEps -> SimpleType -> PrdCns -> Either Error TypeAut
solveConstraintsTwo aut ty pc = do
  let initState = SolverState { sst_gr = aut, sst_cache = [] }
  (start, SolverState aut _) <- runSolverM (typeToGraph (case pc of {Prd -> Pos; Cns -> Neg}) ty) initState
  return $ (removeIslands . removeEpsilonEdges) (aut { ta_starts = [start] })

solveConstraints :: [Constraint] -> [UVar] -> SimpleType -> PrdCns -> Either Error TypeAut
solveConstraints css uvs ty pc = do
  aut <- solveConstraintsOne css uvs
  solveConstraintsTwo aut ty pc

