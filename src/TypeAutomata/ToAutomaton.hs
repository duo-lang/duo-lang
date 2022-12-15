module TypeAutomata.ToAutomaton ( typeToAut ) where


import Control.Monad.Except ( runExcept, Except )
import Control.Monad.Reader
    ( ReaderT(..), asks, MonadReader(..) )
import Control.Monad.State
    ( StateT(..), gets, modify )
import Data.Graph.Inductive.Graph (Node)
import Data.Graph.Inductive.Graph qualified as G
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set qualified as S

import Errors ( Error, throwAutomatonError )
import Pretty.Types ()
import Pretty.Pretty (ppPrint)
import Syntax.TST.Types
import Syntax.RST.Types (PolarityRep(..), Polarity(..), polarityRepToPol)
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCnsRep(..), PrdCns(..))
import Syntax.CST.Names
import Syntax.CST.Kinds
import TypeAutomata.Definition
import Loc ( defaultLoc )
import Utils ( enumerate )
import Control.Monad
import Data.Maybe (fromMaybe, isJust)

--------------------------------------------------------------------------
-- The TypeToAutomaton (TTA) Monad
--------------------------------------------------------------------------

-- | The lookup environment allows to map TVars to Nodes:
--
-- Recursive type variables have a polarity. They are therefore mapped to
-- either `(Just n, Nothing)` or `(Nothing, Just n)`
--
-- Skolem variables exist both positively and negatively. They are therefore
-- mapped to a pair `(n,m)`
data LookupEnv = LookupEnv
  { tSkolemVarEnv :: Map SkolemTVar (Node,Node)
  , tRecVarEnv :: Map RecTVar (Maybe Node, Maybe Node)
  , tCnPosEnv :: Map (Typ Pos) [ClassName]
  , tCnNegEnv :: Map (Typ Neg) [ClassName]
  }

type TTA a = StateT (TypeAutCore EdgeLabelEpsilon) (ReaderT LookupEnv (Except (NonEmpty Error))) a

runTypeAut :: TypeAutCore EdgeLabelEpsilon
           -- ^ The initial TypeAutomaton to start the computation.
           -> LookupEnv
           -- ^ The initial lookup environment.
           -> TTA a
           -- ^ The computation to run.
           -> Either (NonEmpty Error) (a, TypeAutCore EdgeLabelEpsilon)
runTypeAut graph lookupEnv f = runExcept (runReaderT (runStateT f graph) lookupEnv)


-- | Every type variable is mapped to a pair of nodes.
createNodes :: [KindedSkolem] -> [(SkolemTVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)]
createNodes tvars = createNode <$> createPairs tvars
  where
    createNode :: (KindedSkolem, Node, Node) -> (SkolemTVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)
    createNode ((tv, mk), posNode, negNode) = (tv, (posNode, emptyNodeLabel Pos mk []), (negNode, emptyNodeLabel Neg mk []), (negNode, posNode))

    createPairs :: [KindedSkolem] -> [(KindedSkolem, Node,Node)]
    createPairs tvs = (\i -> (tvs !! i, 2 * i, 2 * i + 1)) <$> [0..length tvs - 1]


initialize :: [KindedSkolem] -> Map (Typ Pos) [ClassName] -> Map (Typ Neg) [ClassName] -> (TypeAutCore EdgeLabelEpsilon, LookupEnv)
initialize tvars cnpos cnneg =
  let
    nodes = createNodes tvars
    initAut = TypeAutCore
              { ta_gr = G.mkGraph ([pos | (_,pos,_,_) <- nodes] ++ [neg | (_,_,neg,_) <- nodes]) []
              , ta_flowEdges = [ flowEdge | (_,_,_,flowEdge) <- nodes]
              }
    lookupEnv = LookupEnv { tSkolemVarEnv = M.fromList [(tv, (posNode,negNode)) | (tv,(posNode,_),(negNode,_),_) <- nodes]
                          , tRecVarEnv = M.empty
                          , tCnPosEnv = cnpos
                          , tCnNegEnv = cnneg
                          }
  in
    (initAut, lookupEnv)

lookupClass :: PolarityRep pol -> Typ pol -> TTA [ClassName]
lookupClass PosRep typ = do
  env <- asks tCnPosEnv
  pure $ fromMaybe [] (M.lookup typ env)
lookupClass NegRep tyn = do
  env <- asks tCnNegEnv
  pure $ fromMaybe [] (M.lookup tyn env)

-- | An alternative to `runTypeAut` where the initial state is constructed from a list of Tvars.
runTypeAutTvars :: [KindedSkolem]
                -> Map (Typ Pos) [ClassName]
                -> Map (Typ Neg) [ClassName]
                -> TTA a
                -> Either (NonEmpty Error) (a, TypeAutCore EdgeLabelEpsilon)
runTypeAutTvars tvars cnpos cnneg m = do
  let (aut, env) = initialize tvars cnpos cnneg
  runTypeAut aut env m

--------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------

modifyGraph :: (TypeGrEps -> TypeGrEps) -> TTA ()
modifyGraph f = modify go
  where
    go aut@TypeAutCore { ta_gr } = aut { ta_gr = f ta_gr }

insertNode :: Node -> NodeLabel -> TTA ()
insertNode node nodelabel = modifyGraph (G.insNode (node, nodelabel))

insertEdges :: [(Node,Node,EdgeLabelEpsilon)] -> TTA ()
insertEdges edges = modifyGraph (G.insEdges edges)

newNodeM :: TTA Node
newNodeM = do
  graph <- gets ta_gr
  pure $ (head . G.newNodes 1) graph

lookupTVar :: PolarityRep pol -> SkolemTVar -> TTA Node
lookupTVar PosRep tv = do
  tSkolemVarEnv <- asks tSkolemVarEnv
  case M.lookup tv tSkolemVarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The type variable:"
                                              , "    " <> unSkolemTVar tv
                                              , "is not available in the automaton."
                                              ]
    -- Skolem Variables cannot appear with only one polarity anymore
    --Just (Nothing,_) -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
    --                                                   , "The type variable:"
    --                                                   , "    " <> unSkolemTVar tv
    --                                                   , "exists only at negative polarity."
    --                                                   ]
    Just (pos,_) -> return pos
lookupTVar NegRep tv = do
  tSkolemVarEnv <- asks tSkolemVarEnv
  case M.lookup tv tSkolemVarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The type variable:"
                                              , "    " <> unSkolemTVar tv
                                              , "is not available in the automaton."
                                              ]
    -- Skolem Variables cannot appear with only one polarity anymore
    --Just (_,Nothing) -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
    --                                                   , "The type variable:"
    --                                                   , "    " <> unSkolemTVar tv
    --                                                   , "exists only at positive polarity."
    --                                                   ]
    Just (_,neg) -> return neg

lookupTRecVar :: PolarityRep pol -> RecTVar -> TTA Node
lookupTRecVar PosRep tv = do
  tRecVarEnv <- asks tRecVarEnv
  case M.lookup tv tRecVarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The Recursive Variable:"
                                              , "   " <> unRecTVar tv
                                              , "is not available in the automaton."
                                              ]
    Just (Nothing,_) -> throwAutomatonError defaultLoc ["Could not insert type into automaton."
                                                       , "The Recursive Variable:"
                                                       , "   " <> unRecTVar tv
                                                       , "exists only in negative polarity."
                                                       ]
    Just (Just pos,_) -> return pos
lookupTRecVar NegRep tv = do
  tRecVarEnv <- asks tRecVarEnv
  case M.lookup tv tRecVarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The Recursive Variable:"
                                              , "   " <> unRecTVar tv
                                              , "is not available in the automaton."
                                              ]
    Just (_,Nothing) -> throwAutomatonError defaultLoc ["Could not insert type into automaton."
                                                       , "The Recursive Variable:"
                                                       , "   " <> unRecTVar tv
                                                       , "exists only in positive polarity."
                                                       ]
    Just (_,Just neg) -> return neg



--------------------------------------------------------------------------
-- Inserting a type into an automaton
--------------------------------------------------------------------------

sigToLabel :: XtorSig pol -> XtorLabel
sigToLabel (MkXtorSig name ctxt) = MkXtorLabel name (linearContextToArity ctxt)

insertXtors :: CST.DataCodata -> Polarity -> Maybe RnTypeName -> EvaluationOrder -> [XtorSig pol] -> TTA Node
insertXtors dc pol mtn mk xtors = do
  newNode <- newNodeM
  insertNode newNode (singleNodeLabel pol dc mtn (S.fromList (sigToLabel <$> xtors)) mk)
  forM_ xtors $ \(MkXtorSig xt ctxt) -> do
    forM_ (enumerate ctxt) $ \(i, pcType) -> do
      node <- insertPCType pcType
      insertEdges [(newNode, node, EdgeSymbol dc xt (case pcType of (PrdCnsType PrdRep _)-> Prd; (PrdCnsType CnsRep _) -> Cns) i)]
  return newNode

insertPCType :: PrdCnsType pol -> TTA Node
insertPCType (PrdCnsType _ ty) = insertType ty

insertVariantType :: VariantType pol -> TTA (Node, Variance)
insertVariantType (CovariantType ty) = do
  node <- insertType ty
  pure (node, Covariant)
insertVariantType (ContravariantType ty) = do
  node <- insertType ty
  pure (node, Contravariant)

insertType :: Typ pol -> TTA Node
insertType (TySkolemVar _ rep _ tv) = lookupTVar rep tv
insertType (TyUniVar loc _ _ tv) = throwAutomatonError loc [ "Could not insert type into automaton."
                                                                   , "The unification variable:"
                                                                   , "    " <> unUniTVar tv
                                                                   , "should not appear at this point in the program."
                                                                   ]
insertType (TyRecVar _ rep _ tv) = lookupTRecVar rep tv
insertType ty@(TyTop _ knd) = do
  newNode <- newNodeM
  cns <- lookupClass NegRep ty
  insertNode newNode (emptyNodeLabel Neg knd cns)
  pure newNode
insertType ty@(TyBot _ knd) = do
  newNode <- newNodeM
  cns <- lookupClass PosRep ty
  insertNode newNode (emptyNodeLabel Pos knd cns)
  pure newNode
insertType ty@(TyUnion _ knd ty1 ty2) = do
  newNode <- newNodeM
  cns <- lookupClass PosRep ty
  insertNode newNode (emptyNodeLabel Pos knd cns)
  ty1' <- insertType ty1
  ty2' <- insertType ty2
  insertEdges [(newNode, ty1', EpsilonEdge ()), (newNode, ty2', EpsilonEdge ())]
  pure newNode
insertType ty@(TyInter _ knd ty1 ty2) = do
  newNode <- newNodeM
  cns <- lookupClass NegRep ty
  insertNode newNode (emptyNodeLabel Neg knd cns)
  ty1' <- insertType ty1
  ty2' <- insertType ty2
  insertEdges [(newNode, ty1', EpsilonEdge ()), (newNode, ty2', EpsilonEdge ())]
  pure newNode
insertType ty'@(TyRec _ rep rv ty) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  cns <- lookupClass rep ty'
  insertNode newNode (emptyNodeLabel pol (getKind ty) cns)
  let extendEnv PosRep (LookupEnv tSkolemVars tRecVars tCnPosEnv tCnNegEnv) = LookupEnv tSkolemVars (M.insert rv (Just newNode, Nothing) tRecVars) tCnPosEnv tCnNegEnv
      extendEnv NegRep (LookupEnv tSkolemVars tRecVars tCnPosEnv tCnNegEnv) = LookupEnv tSkolemVars (M.insert rv (Nothing, Just newNode) tRecVars) tCnPosEnv tCnNegEnv
  n <- local (extendEnv rep) (insertType ty)
  insertEdges [(newNode, n, EpsilonEdge ())]
  return newNode
insertType (TyData _  polrep (CBox mk) xtors) = insertXtors CST.Data (polarityRepToPol polrep) Nothing mk xtors
insertType (TyData _ _ mk _) = throwAutomatonError defaultLoc ["Tried to insert TyData into automaton with incorrect kind " <> ppPrint mk]
insertType (TyCodata _ polrep (CBox mk)  xtors) = insertXtors CST.Codata (polarityRepToPol polrep) Nothing mk xtors
insertType (TyCodata _ _ mk _) = throwAutomatonError defaultLoc ["Tried to insert TyCodata into automaton with incorrect kind " <> ppPrint mk]
insertType (TyDataRefined _ polrep (CBox mk) mtn xtors) = insertXtors CST.Data   (polarityRepToPol polrep) (Just mtn) mk xtors
insertType (TyDataRefined _ _ mk _ _) = throwAutomatonError defaultLoc ["Tried to insert TyDataRefined into automaton with incorrect kind " <> ppPrint mk]
insertType (TyCodataRefined _ polrep (CBox mk) mtn xtors) = insertXtors CST.Codata (polarityRepToPol polrep) (Just mtn) mk xtors
insertType (TyCodataRefined _ _ mk _ _) = throwAutomatonError defaultLoc ["Tried to insert TyCodataRefined into automaton with incorrect kind " <> ppPrint mk]
insertType (TySyn _ _ _ ty) = insertType ty
insertType ty@(TyNominal _ rep mk tn args) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  cns <- lookupClass rep ty
  insertNode newNode ((emptyNodeLabel pol mk cns) { nl_nominal = S.singleton (tn, toVariance <$> args) })
  argNodes <- forM args insertVariantType
  insertEdges ((\(i, (n, variance)) -> (newNode, n, TypeArgEdge tn variance i)) <$> enumerate argNodes)
  return newNode
insertType (TyI64 _ rep) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol I64)
  return newNode
insertType (TyF64 _ rep) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol F64)
  return newNode
insertType (TyChar _ rep) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol PChar)
  return newNode
insertType (TyString _ rep) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol PString)
  return newNode
insertType (TyFlipPol _ _) =
  throwAutomatonError defaultLoc ["Tried to insert TyFlipPol into type automaton"]

--------------------------------------------------------------------------
--
--------------------------------------------------------------------------


-- turns a type into a type automaton with prescribed start polarity.
typeToAut :: TypeScheme pol -> Either (NonEmpty Error) (TypeAutEps pol)
typeToAut TypeScheme { ts_vars, ts_monotype, ts_constraints } = do
  let (cnpos, cnneg) = M.spanAntitone (isJust . fst) $ foldr (\c m -> (case c of (TypeClassConstraint cn tVar) -> M.insertWith (++) tVar [cn]; _ -> id) m) M.empty ts_constraints
  let cnpos' = M.mapKeys (\(x,_) -> case x of Nothing -> error "Unexpected error in typeToAut: spanAntitone went wrong."; Just typ -> typ) cnpos
  let cnneg' = M.mapKeys (\(_,x) -> case x of Nothing -> error "Unexpected error in typeToAut: type class constraint is neither co- nor contravariant."; Just typ -> typ) cnneg
  (start, aut) <- runTypeAutTvars ts_vars cnpos' cnneg' (insertType ts_monotype)
  return TypeAut { ta_pol = getPolarity ts_monotype
                 , ta_starts = [start]
                 , ta_core = aut
                 }
