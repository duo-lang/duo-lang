module TypeAutomata.RemoveAdmissible
  ( removeAdmissableFlowEdges
  ) where

import Control.Applicative ((<|>))
import Control.Monad (guard, forM_)
import Data.Graph.Inductive.Graph
import Data.Maybe (fromMaybe)
import Data.Set qualified as S
import Data.Tuple (swap)

import Syntax.CST.Types ( DataCodata(Codata, Data), PrdCns(..))
import Syntax.RST.Types (Polarity(..))
import TypeAutomata.Definition
import Control.Monad.State.Strict (MonadState (get, put), modify, gets, State, runState)
import GHC.Base (Alternative)
import qualified GHC.Base as A (empty)
import Data.Bifunctor (first)

----------------------------------------------------------------------------------------
-- Removal of admissible flow edges.
--
-- The removal of admissible flow edges is part of the type simplification process.
-- In our representation of type automata, a type variable is represented by a flow edge
-- connecting two nodes. For example, "forall a. a -> a" is represented as
--
--            ----------------
--       -----| { Ap(_)[_] } |------
--       |    ----------------     |
--       |                         |
--       |Ap(1)                    |Ap[1]
--       |                         |
--   ----------        a       ----------
--   |        |~~~~~~~~~~~~~~~~|        |
--   ----------                ----------
--
--  But in some cases the flow edge is admissible. Consider the following automaton:
--
--            ----------------
--       -----| { Ap(_)[_] } |------
--       |    ----------------     |
--       |                         |
--       |Ap(1)                    |Ap[1]
--       |                         |
--   ----------        a       ----------
--   | Int    |~~~~~~~~~~~~~~~~|  Int   |
--   ----------                ----------
--
-- This automaton would be turned into the type "forall a. a /\ Int -> a \/ Int".
-- The admissibility check below recognizes that the flow edge "a" can be removed,
-- which results in the following automaton.
--
--            ----------------
--       -----| { Ap(_)[_] } |------
--       |    ----------------     |
--       |                         |
--       |Ap(1)                    |Ap[1]
--       |                         |
--   ----------                ----------
--   | Int    |                |  Int   |
--   ----------                ----------
--
-- This automaton is rendered as the (simpler) type "Int -> Int".
--
----------------------------------------------------------------------------------------

data AdmissableS = AdmissableS { memo :: S.Set FlowEdge, blacklist :: S.Set FlowEdge }
newtype AdmissableM a = AdmissableM { runAdmissable :: State AdmissableS (Maybe a) }
  deriving (Functor)

instance Applicative AdmissableM where
  pure = AdmissableM . pure . pure
  ff <*> fa = AdmissableM $ do
    s <- get
    let (mf, s') = runState (runAdmissable ff) s
    let (ma, s'') = runState (runAdmissable fa) s'
    put s''
    return $ mf <*> ma

instance Monad AdmissableM where
  return = pure
  ma >>= f = AdmissableM $ do
    s <- get
    let (ma', s') = runState (runAdmissable ma) s
    case ma' of
      Nothing -> put s' >> return Nothing
      (Just a) -> do
        let (mb, s'') = runState (runAdmissable (f a)) s'
        put s''
        return mb

instance MonadState AdmissableS AdmissableM where
  get = AdmissableM $ Just <$> get
  put s = AdmissableM $ do
      put s
      return $ Just ()

instance Alternative AdmissableM where
  (AdmissableM l) <|> (AdmissableM r) = AdmissableM $ do
    (ml, s') <- runState l <$> get
    case ml of
      Nothing -> do
          let (mr, s'') = runState r s'
          put s''
          return mr
      (Just a) -> return $ Just a
  empty = AdmissableM $ pure Nothing

instance MonadFail AdmissableM where
  fail _s = liftAM Nothing

execAdmissable :: AdmissableM a -> (a, AdmissableS)
execAdmissable = first (fromMaybe (error "should not happen")) . flip runState AdmissableS { memo = S.empty, blacklist = S.empty } . runAdmissable

liftAM :: Maybe a -> AdmissableM a
liftAM = AdmissableM . pure

sucWith :: TypeGr -> Node -> EdgeLabelNormal -> AdmissableM Node
sucWith gr i el = liftAM $ lookup el (map swap (lsuc gr i))

modifyMemo :: (S.Set FlowEdge -> S.Set FlowEdge) -> AdmissableM ()
modifyMemo f = modify $ \s -> s { memo = f $ memo s }

insertFE :: FlowEdge -> AdmissableM ()
insertFE = modifyMemo . S.insert

blacklistFE :: FlowEdge -> AdmissableM ()
blacklistFE fe =
  modify $ \s -> s { memo = fe `S.delete` memo s, blacklist = fe `S.insert` blacklist s }

isMemoised :: FlowEdge -> AdmissableM ()
isMemoised fe = do
  m <- gets memo
  guard $ fe `S.member` m

isBlacklisted :: FlowEdge -> AdmissableM ()
isBlacklisted fe = do
  b <- gets blacklist
  guard $ fe `S.member` b

subtypeData :: TypeAutCore EdgeLabelNormal -> FlowEdge -> AdmissableM ()
subtypeData aut@TypeAutCore{ ta_gr } (i,j) = do
  (MkNodeLabel Neg (Just dat1) _ _ _ _ _) <- liftAM $ lab ta_gr i
  (MkNodeLabel Pos (Just dat2) _ _ _ _ _) <- liftAM $ lab ta_gr j
  -- Check that all constructors in dat1 are also in dat2.
  forM_ (S.toList dat1) $ \xt -> guard (xt `S.member` dat2)
  -- Check arguments of each constructor of dat1.
  forM_ (labelName <$> S.toList dat1) $ \xt -> do
    forM_ [(n,el) | (n, el@(EdgeSymbol Data xt' Prd _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
      m <- sucWith ta_gr j el
      admissableM aut (n,m)
    forM_ [(n,el) | (n, el@(EdgeSymbol Data xt' Cns _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
      m <- sucWith ta_gr j el
      admissableM aut (m,n)

subtypeCodata :: TypeAutCore EdgeLabelNormal -> FlowEdge -> AdmissableM ()
subtypeCodata aut@TypeAutCore{ ta_gr } (i,j) = do
  (MkNodeLabel Neg _ (Just codat1) _ _ _ _) <- liftAM $ lab ta_gr i
  (MkNodeLabel Pos _ (Just codat2) _ _ _ _) <- liftAM $ lab ta_gr j
  -- Check that all destructors of codat2 are also in codat1.
  forM_ (S.toList codat2) $ \xt -> guard (xt `S.member` codat1)
  -- Check arguments of all destructors of codat2.
  forM_ (labelName <$> S.toList codat2) $ \xt -> do
    forM_ [(n,el) | (n, el@(EdgeSymbol Codata xt' Prd _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
      m <- sucWith ta_gr j el
      admissableM aut (m,n)
    forM_ [(n,el) | (n, el@(EdgeSymbol Codata xt' Cns _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
      m <- sucWith ta_gr j el
      admissableM aut (n,m)

subtypeNominal :: TypeAutCore EdgeLabelNormal -> FlowEdge -> AdmissableM ()
subtypeNominal TypeAutCore{ ta_gr } (i,j) = do
  (MkNodeLabel Neg _ _ nominal1 _  _ _) <- liftAM $ lab ta_gr i
  (MkNodeLabel Pos _ _ nominal2 _  _ _) <- liftAM $ lab ta_gr j
  guard $ not . S.null $ S.intersection nominal1 nominal2

admissableM :: TypeAutCore EdgeLabelNormal -> FlowEdge -> AdmissableM ()
admissableM aut@TypeAutCore{} e =
  isMemoised e <|>
  isBlacklisted e <|>
    do  insertFE e
        subtypeData aut e <|>
          subtypeCodata aut e <|>
          subtypeNominal aut e <|>
          blacklistFE e

removeAdmissableFlowEdges :: TypeAutDet pol -> TypeAutDet pol
removeAdmissableFlowEdges aut@TypeAut{ ta_core = tac@TypeAutCore {..}} =
  aut { ta_core = tac { ta_flowEdges = ta_flowEdges_filtered }}
    where
      ta_flowEdges_filtered :: [FlowEdge]
      ta_flowEdges_filtered = filter (not . flip S.member admissable) ta_flowEdges

      admissable :: S.Set FlowEdge
      admissable = memo $ snd $ execAdmissable $ mapM (admissableM tac) ta_flowEdges
