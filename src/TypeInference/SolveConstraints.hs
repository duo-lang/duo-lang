module TypeInference.SolveConstraints
  ( solveConstraints,
    KindPolicy(..)
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable (find)
import Data.List.NonEmpty qualified as NE
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.List (partition)
import Data.Maybe (fromJust, isJust)
import Data.Bifunctor (second)

import Driver.Environment (Environment)
import Errors
import Syntax.TST.Types
import Syntax.RST.Types (PolarityRep(..), Polarity(..))
import Pretty.Pretty
import Pretty.Types ()
import Pretty.Constraints ()
import TypeInference.Constraints
import Loc ( defaultLoc )
import Syntax.CST.Names
import Syntax.CST.Types ( PrdCnsRep(..))
import Syntax.CST.Kinds

------------------------------------------------------------------------------
-- Constraint solver monad
------------------------------------------------------------------------------

data SolverState = SolverState
  { sst_bounds :: Map UniTVar VariableState
  , sst_cache :: Map (Constraint ()) SubtypeWitness -- The constraints in the cache need to have their annotations removed!
  , sst_kvars :: [([KVar], Maybe MonoKind)]
  }

createInitState :: ConstraintSet -> SolverState
createInitState (ConstraintSet _ uvs kuvs) =
  SolverState { sst_bounds =  M.fromList $ getsst_bounds uvs --[(fst uv,emptyVarState (KindVar (MkKVar "TODO"))) | uv <- uvs]
              , sst_cache = M.empty
              , sst_kvars = [([kv],Nothing) | kv <- kuvs]
              }
  where 
    getsst_bounds :: [(UniTVar, UVarProvenance, MonoKind)] -> [(UniTVar, VariableState)]
    getsst_bounds [] = []
    getsst_bounds ((uv,_,mk):rst) = (uv,emptyVarState mk):getsst_bounds rst


type SolverM = (ReaderT (Map ModuleName Environment, ()) (StateT SolverState (Except (NE.NonEmpty Error))))

runSolverM :: SolverM a -> Map ModuleName Environment -> SolverState -> Either (NE.NonEmpty Error) (a, SolverState)
runSolverM m env initSt = runExcept (runStateT (runReaderT m (env,())) initSt)

------------------------------------------------------------------------------
-- Monadic helper functions
------------------------------------------------------------------------------

addToCache :: Constraint a -> SubtypeWitness -> SolverM ()
addToCache cs w = modifyCache (M.insert (void cs) w) -- We delete the annotation when inserting into cache

modifyCache :: (Map (Constraint ()) SubtypeWitness -> Map (Constraint ()) SubtypeWitness) -> SolverM ()
modifyCache f = modify (\(SolverState gr cache kvars) -> SolverState gr (f cache) kvars)

inCache :: Constraint a -> SolverM Bool
inCache cs = gets sst_cache >>= \cache -> pure (void cs `M.member` cache)

modifyBounds :: (VariableState -> VariableState) -> UniTVar -> SolverM ()
modifyBounds f uv = modify (\(SolverState varMap cache kvars) -> SolverState (M.adjust f uv varMap) cache kvars)


getBounds :: UniTVar -> SolverM VariableState
getBounds uv = do
  bounds <- gets sst_bounds
  case M.lookup uv bounds of
    Nothing -> throwSolverError defaultLoc [ "Tried to retrieve bounds for variable:"
                                           , ppPrint uv
                                           , "which is not a valid unification variable."
                                           ]
    Just vs -> return vs

getKVars :: SolverM [([KVar],Maybe MonoKind)]
getKVars = gets sst_kvars

putKVars :: [([KVar],Maybe MonoKind)] -> SolverM ()
putKVars x = modify (\s -> s { sst_kvars = x })

addUpperBound :: Delay a -> UniTVar -> Typ Neg -> SolverM [Constraint (Delay ConstraintInfo)]
addUpperBound del uv ty = do
  modifyBounds (\(VariableState ubs lbs classes kind) -> VariableState (ty:ubs) lbs classes kind) uv
  bounds <- getBounds uv
  let lbs = vst_lowerbounds bounds
  return [SubType (UpperBoundConstraint <$ del) lb ty | lb <- lbs]

addLowerBound :: Delay a -> UniTVar -> Typ Pos -> SolverM [Constraint (Delay ConstraintInfo)]
addLowerBound del uv ty = do
  modifyBounds (\(VariableState ubs lbs classes kind) -> VariableState ubs (ty:lbs) classes kind) uv
  bounds <- getBounds uv
  let ubs = vst_upperbounds bounds
  return [SubType (LowerBoundConstraint <$ del) ty ub | ub <- ubs]

addTypeClassConstraint :: UniTVar -> ClassName -> SolverM ()
addTypeClassConstraint uv cn = modifyBounds (\(VariableState ubs lbs classes kind) -> VariableState ubs lbs (cn:classes) kind) uv

-- lookupKVar :: KVar -> Map (Maybe MonoKind) (Set KVar) -> SolverM (Maybe MonoKind, Set KVar)
-- lookupKVar kv mp = case M.toList (M.filter (\x -> kv `elem` x) mp) of 
--   [] -> throwSolverError defaultLoc ["Kind variable not found."]
--   [(mk,set)] -> pure (mk,set)
--   _ -> throwSolverError defaultLoc ["Multiple kinds for kind variable" <> T.pack (show kv)]

------------------------------------------------------------------------------
-- Constraint solving algorithm
------------------------------------------------------------------------------

solve :: [Constraint (Delay ConstraintInfo)] -> SolverM ()
solve [] = return ()
solve (cs:css) = do
  cacheHit <- inCache cs
  if cacheHit then solve css else
    case cs of
      (KindEq _ k1 k2) -> do
        unifyKinds k1 k2
        solve css
      (SubType del (TyUniVar _ PosRep _ uvl) tvu@(TyUniVar _ NegRep _ uvu)) ->
        if uvl == uvu
        then addToCache cs (UVarB uvl uvu) >> solve css
        else do
          addToCache cs (UVarB uvl uvu)
          newCss <- addUpperBound del uvl tvu
          solve (newCss ++ css)
      (SubType del (TyUniVar _ PosRep _ uv) ub) -> do
        addToCache cs (UVarL uv ub)
        newCss <- addUpperBound del uv ub
        solve (newCss ++ css)
      (SubType del lb (TyUniVar _ NegRep _ uv)) -> do
        addToCache cs (UVarR uv lb)
        newCss <- addLowerBound del uv lb
        solve (newCss ++ css)
      (TypeClassPos _ cn (TyUniVar _ PosRep _ uv)) -> do
        addTypeClassConstraint uv cn
      (TypeClassNeg _ cn (TyUniVar _ NegRep _ uv)) -> do
        addTypeClassConstraint uv cn
      _ -> do
        (w, subCss) <- subConstraints cs
        addToCache cs w
        solve (subCss ++ css)

------------------------------------------------------------------------------
-- Kind Inference
------------------------------------------------------------------------------

partitionM :: [([KVar], Maybe MonoKind)] -> KVar -> SolverM (([KVar], Maybe MonoKind),[([KVar], Maybe MonoKind)])
partitionM sets kv = do
  case partition (\x -> kv `elem` fst x) sets of
    ([], _) -> throwSolverError defaultLoc ["Kind variable cannot be found: " <> ppPrint kv]
    ([fst],rest) -> pure (fst, rest)
    (_:_:_,_) -> throwSolverError defaultLoc ["Kind variable occurs in more than one equivalence class: " <> ppPrint kv]

unifyKinds :: MonoKind -> MonoKind -> SolverM ()
unifyKinds (CBox cc1) (CBox cc2) =
  if cc1 == cc2
    then pure ()
    else throwSolverError defaultLoc ["Cannot unify incompatible kinds: " <> ppPrint cc1 <> " and " <> ppPrint cc2]
unifyKinds (KindVar kv1) (KindVar kv2) = do
  sets <- getKVars
  ((kvset1,mk1),rest1) <- partitionM sets kv1
  if kv2 `elem` kvset1 then
    pure ()
  else do
    ((kvset2,mk2), rest2) <- partitionM rest1 kv2
    let newSet = kvset1 ++ kvset2
    case (mk1,mk2) of
      (mk1, Nothing) -> putKVars $ (newSet,mk1):rest2
      (Nothing, mk2) -> putKVars $ (newSet,mk2):rest2
      (Just mk1, Just mk2) | mk1 == mk2 -> putKVars $ (newSet, Just mk1) :rest2
                           | otherwise -> throwSolverError defaultLoc ["Cannot unify incompatiple kinds: " <> ppPrint mk1 <> " and " <> ppPrint mk2]
unifyKinds (KindVar kv) kind = do
  sets <- getKVars
  ((kvset,mk),rest) <- partitionM sets kv
  case mk of
    Nothing -> putKVars $ (kvset, Just kind):rest
    Just mk -> if kind == mk
               then return ()
               else throwSolverError defaultLoc ["Cannot unify incompatible kinds: " <> ppPrint kind <> " and " <> ppPrint mk]
unifyKinds kind (KindVar kv) = unifyKinds (KindVar kv) kind
unifyKinds I64Rep I64Rep = return ()
unifyKinds F64Rep F64Rep = return ()
unifyKinds CharRep CharRep = return ()
unifyKinds StringRep StringRep = return ()
unifyKinds knd1 knd2 = throwSolverError defaultLoc ["Cannot unify incompatible kinds: " <> ppPrint knd1<> " and " <> ppPrint knd2]

computeKVarSolution :: KindPolicy
                    -> [([KVar], Maybe MonoKind)]
                    -> Either (NE.NonEmpty Error) (Map KVar MonoKind)
computeKVarSolution DefaultCBV sets = return $ computeKVarSolution' ((\(xs,mk) -> case mk of Nothing -> (xs,CBox CBV); Just mk -> (xs,mk)) <$> sets)
computeKVarSolution DefaultCBN sets = return $ computeKVarSolution' ((\(xs,mk) -> case mk of Nothing -> (xs,CBox CBN); Just mk -> (xs,mk)) <$> sets)
computeKVarSolution ErrorUnresolved sets = if all (\(_,mk) -> isJust mk) sets
                                           then return $ computeKVarSolution' (map (Data.Bifunctor.second fromJust) sets)
                                           else Left $  (NE.:| []) $  ErrConstraintSolver $ SomeConstraintSolverError defaultLoc "Not all kind variables could be resolved"
computeKVarSolution' :: [([KVar],MonoKind)] -> Map KVar MonoKind
computeKVarSolution' sets = M.fromList (concatMap f sets)
  where
    f :: ([a],MonoKind) -> [(a,MonoKind)]
    f (xs, mk) = zip xs (repeat mk)


data KindPolicy
  = DefaultCBV
  | DefaultCBN
  | ErrorUnresolved
  deriving (Show, Eq)
------------------------------------------------------------------------------
-- Computing Subconstraints
------------------------------------------------------------------------------

lookupXtor :: XtorName -> [XtorSig pol] -> SolverM (XtorSig pol)
lookupXtor xtName xtors = case find (\(MkXtorSig xtName' _) -> xtName == xtName') xtors of
  Nothing -> throwSolverError defaultLoc ["The xtor"
                                         , ppPrint xtName
                                         , "is not contained in the list of xtors"
                                         , ppPrint xtors ]
  Just xtorSig -> pure xtorSig

checkXtor :: Delay a -> [XtorSig Neg] -> XtorSig Pos ->  SolverM [Constraint (Delay ConstraintInfo)]
checkXtor del xtors2 (MkXtorSig xtName subst1) = do
  MkXtorSig _ subst2 <- lookupXtor xtName xtors2
  checkContexts del subst1 subst2

checkContexts :: Delay a -> LinearContext Pos -> LinearContext Neg -> SolverM [Constraint (Delay ConstraintInfo)]
checkContexts _ [] [] = return []
checkContexts del (PrdCnsType PrdRep ty1:rest1) (PrdCnsType PrdRep ty2:rest2) = do
  xs <- checkContexts del rest1 rest2
  return (SubType (XtorSubConstraint <$ del) ty1 ty2:xs)
checkContexts del (PrdCnsType CnsRep ty1:rest1) (PrdCnsType CnsRep ty2:rest2) = do
  xs <- checkContexts del rest1 rest2
  return (SubType (XtorSubConstraint <$ del) ty2 ty1:xs)
checkContexts _ (PrdCnsType PrdRep _:_) (PrdCnsType CnsRep _:_) =
  throwSolverError defaultLoc ["checkContexts: Tried to constrain PrdType by CnsType."]
checkContexts _ (PrdCnsType CnsRep _:_) (PrdCnsType PrdRep _:_) =
  throwSolverError defaultLoc ["checkContexts: Tried to constrain CnsType by PrdType."]
checkContexts _ []    (_:_) =
  throwSolverError defaultLoc ["checkContexts: Linear contexts have unequal length."]
checkContexts _ (_:_) []    =
  throwSolverError defaultLoc ["checkContexts: Linear contexts have unequal length."]


-- | The `subConstraints` function takes a complex constraint, and decomposes it
-- into simpler constraints. A constraint is complex if it is not atomic. An atomic
-- constraint has a type variable on the right or left hand side of the constraint.
-- 
-- Besides generating subconstraints the function returns a witness for the subtyping
-- relation. 
-- This can be seen as a means to reconstruct the original constraint or to provide a
-- coercion function from the super- to the subtype.
-- The constructor `SubVar` is a sort of hole which will later on be filled with new
-- witnesses for the subconstraints.
--
-- The `subConstraints` function is the function which will produce the error if the
-- constraint set generated from a program is not solvable.
subConstraints :: Constraint (Delay ConstraintInfo) -> SolverM (SubtypeWitness, [Constraint (Delay ConstraintInfo)])
-- Type synonyms are unfolded and are not preserved through constraint solving.
-- A more efficient solution to directly compare type synonyms is possible in the
-- future.
subConstraints c@(SubType annot (TySyn _ _ rn ty) ty') =
  pure (SynL rn (SubVar c), [SubType annot ty ty'])
subConstraints c@(SubType annot ty (TySyn _ _ rn ty')) =
  pure (SynR rn (SubVar c), [SubType annot ty ty'])
-- Intersection and union constraints:
--
-- If the left hand side of the constraint is a intersection type, or the
-- right hand side is a union type, then the constraint can be directly decomposed
-- into structurally smaller subconstraints. E.g.:
--
--     ty1 \/ ty2 <: ty3         ~>     ty1 <: ty3   AND  ty2 <: ty3
--     ty1 <: ty2 /\ ty3         ~>     ty1 <: ty2   AND  ty1 <: ty3
--
subConstraints (SubType _ typ (TyTop _ _)) =
  pure (FromTop typ, [])
subConstraints (SubType _ (TyBot _ _) tyn) =
  pure (ToBot tyn, [])
subConstraints (SubType del (TyUnion _ _ ty1 ty2) ty3) = do
  let c1 = SubType (IntersectionUnionSubConstraint <$ del) ty1 ty3
  let c2 = SubType (IntersectionUnionSubConstraint <$ del) ty2 ty3
  pure (Join (SubVar c1) (SubVar c2), [c1, c2])
subConstraints (SubType del ty1 (TyInter _ _ ty2 ty3)) = do
  let c1 = SubType (IntersectionUnionSubConstraint <$ del) ty1 ty2
  let c2 = SubType (IntersectionUnionSubConstraint <$ del) ty1 ty3
  pure (Meet (SubVar c1) (SubVar c2), [c1, c2])
-- Recursive constraints:
--
-- If the left hand side or the right hand side of the constraint is a recursive
-- mu-type, the recursive variable is inserted into the left map of the /Delay/ annotation.
-- Note that this case makes it non-obvious
-- that constraint generation is going to terminate. Examples:
--
--     rec a.ty1 <: ty2          ~>     ty1 [rec a.ty1 / a] <: ty2
--     ty1 <: rec a.ty2          ~>     ty1 <: ty2 [rec a.ty2 / a]
--
subConstraints (SubType del rc@(TyRec _ _ recTVar ty) ty') = do
  let c = SubType (RecTypeSubConstraint <$ addDelayL recTVar rc del) ty ty'
  return (UnfoldL recTVar (SubVar c), [c])
subConstraints (SubType del ty' rc@(TyRec _ _ recTVar ty)) = do
  let c = SubType (RecTypeSubConstraint <$ addDelayR recTVar rc del) ty' ty
  return (UnfoldR recTVar (SubVar c), [c])
-- If a recursive type variable is found, we check the /Delay/ annotation for the
-- binding of the variable and generate a subconstraint with the substituted type.
subConstraints (SubType del (TyRecVar _ _ _ recTVar) ty') = do
  case M.lookup recTVar (mapL del) of
      Nothing -> throwSolverError defaultLoc [ "Failed LookupL for recursive variable: " <> ppPrint recTVar ]
      Just ty -> do
        let c = SubType (RecTypeSubConstraint <$ del) ty ty'
        pure (LookupL recTVar (SubVar c), [c])
subConstraints (SubType del ty (TyRecVar _ _ _ recTVar)) = do
  case M.lookup recTVar (mapR del) of
      Nothing -> throwSolverError defaultLoc [ "Failed LookupR for recursive variable: " <> ppPrint recTVar ]
      Just ty' -> do
        let c = SubType (RecTypeSubConstraint <$ del) ty ty'
        pure (LookupR recTVar (SubVar c), [c])
-- Constraints between structural data or codata types:
--
-- Constraints between structural data and codata types generate constraints based
-- on the xtors of the two types. In order to generate the constraints, the helper
-- function `checkXtors` is invoked.
--
--     < ctors1 > <: < ctors2 >  ~>     [ checkXtors ctors2 ctor | ctor <- ctors1 ]
--     { dtors1 } <: { dtors2 }  ~>     [ checkXtors dtors1 dtor | dtor <- dtors2 ]
--
subConstraints (SubType del (TyData _ PosRep _ ctors1) (TyData _ NegRep _ ctors2)) = do
  constraints <- forM ctors1 (checkXtor del ctors2)
  pure (Data $ SubVar <$> concat constraints, concat constraints)

subConstraints (SubType del (TyCodata _ PosRep _ dtors1) (TyCodata _ NegRep _ dtors2)) = do
  constraints <- forM dtors2 (checkXtor del dtors1)
  pure (Codata $ SubVar <$> concat constraints, concat constraints)

-- Constraints between refinement data or codata types:
--
-- These constraints are treated in the same way as those between structural (co)data types, with
-- the added condition that the type names must match. E.g.
--
--     {{ Nat :>> < ctors1 > }} <: {{ Nat  :>> < ctors2 > }}   ~>    [ checkXtors ctors2 ctor | ctor <- ctors1 ]
--     {{ Nat :>> < ctors1 > }} <: {{ Bool :>> < ctors2 > }}   ~>    FAIL
--
subConstraints (SubType del (TyDataRefined _ PosRep _ tn1 ctors1) (TyDataRefined _ NegRep _ tn2 ctors2)) | tn1 == tn2 = do
  constraints <- forM ctors1 (checkXtor del ctors2)
  pure (DataRefined tn1 $ SubVar <$> concat constraints, concat constraints)

subConstraints (SubType del (TyCodataRefined _ PosRep _ tn1 dtors1) (TyCodataRefined _ NegRep _ tn2 dtors2))  | tn1 == tn2 = do
  constraints <- forM dtors2 (checkXtor del dtors1)
  pure (CodataRefined tn1 $ SubVar <$> concat constraints, concat constraints)

-- Constraints between nominal types:
--
-- We currently do not have any subtyping relationships between nominal types.
-- We therefore only have to check if the two nominal types are identical. E.g.:
--
--     Bool <: Nat               ~>     FAIL
--     Bool <: Bool              ~>     []
--
subConstraints (SubType del (TyNominal _ _ _ tn1 args1) (TyNominal _ _ _ tn2 args2)) | tn1 == tn2 = do
    let f (CovariantType ty1) (CovariantType ty2) = SubType (NominalSubConstraint <$ del) ty1 ty2
        f (ContravariantType ty1) (ContravariantType ty2) = SubType (NominalSubConstraint <$ del) ty2 ty1
        f _ _ = error "cannot occur"
        constraints = zipWith f args1 args2
    pure (DataNominal tn1 $ SubVar <$> constraints, constraints)
-- Constraints between primitive types:
subConstraints (SubType _ p@(TyI64 _ _) n@(TyI64 _ _)) = pure (Refl p n, [])
subConstraints (SubType _ p@(TyF64 _ _) n@(TyF64 _ _)) = pure (Refl p n, [])
subConstraints (SubType _ p@(TyChar _ _) n@(TyChar _ _)) = pure (Refl p n, [])
subConstraints (SubType _ p@(TyString _ _) n@(TyString _ _)) = pure (Refl p n, [])
-- All other constraints cannot be solved.
subConstraints (SubType _ t1 t2) = do
  throwSolverError defaultLoc ["Cannot constraint type"
                              , "    " <> ppPrint t1
                              , "by type"
                              , "    " <> ppPrint t2 ]
-- subConstraints for type classes are deprecated
-- type class constraints should only be resolved after subtype constraints
subConstraints TypeClassPos{} = throwSolverError defaultLoc ["subContraints should not be called on type class Constraints"]
subConstraints TypeClassNeg{} = throwSolverError defaultLoc ["subContraints should not be called on type class Constraints"]
subConstraints KindEq{} = throwSolverError defaultLoc ["subContraints should not be called on Kind Equality Constraints"]

-- | Substitute cached witnesses for generated subtyping witness variables.
substitute :: ReaderT (Set (Constraint ())) SolverM ()
substitute = do
    cache <- gets sst_cache
    forM_ (M.toList cache) $ \(c,w) -> do
      w <- go cache w
      lift $ modifyCache (M.adjust (const w) c)
  where
    go :: Map (Constraint ()) SubtypeWitness -> SubtypeWitness -> ReaderT (Set (Constraint ())) SolverM SubtypeWitness
    go m (SynL rn w) = SynL rn <$> go m w
    go m (SynR rn w) = SynR rn <$> go m w
    go _ (FromTop ty) = pure $ FromTop ty
    go _ (ToBot ty) = pure $ ToBot ty
    go m (Meet w1 w2) = Meet <$> go m w1 <*> go m w2
    go m (Join w1 w2) = Join <$> go m w1 <*> go m w2
    go m (UnfoldL recTVar w) = UnfoldL recTVar <$> go m w
    go m (UnfoldR recTVar w) = UnfoldR recTVar <$> go m w
    go m (LookupL recTVar w) = LookupL recTVar <$> go m w
    go m (LookupR recTVar w) = LookupR recTVar <$> go m w
    go m (Data ws) = Data <$> mapM (go m) ws
    go m (Codata ws) = Codata <$> mapM (go m) ws
    go m (DataRefined rn ws) = DataRefined rn <$> mapM (go m) ws
    go m (CodataRefined rn ws) = CodataRefined rn <$> mapM (go m) ws
    go m (DataNominal rn ws) = DataNominal rn <$> mapM (go m) ws
    go _ (Refl typ tyn) = pure $ Refl typ tyn
    go _ (UVarB uv1 uv2) = pure $ UVarB uv1 uv2
    go _ (UVarL uv tyn) = pure $ UVarL uv tyn
    go _ (UVarR uv typ) = pure $ UVarR uv typ
    go _ (Fix cs) = pure $ Fix cs
    go m (SubVar c) = case M.lookup (void c) m of
         Nothing -> throwSolverError defaultLoc [ "Cannot find witness for: " <> ppPrint (extractDelay <$> c) ]
         Just (SubVar _c) -> throwSolverError defaultLoc [ "Tried to substitute a variable with another variable" ]
         Just w -> asks (S.member (void c)) >>= \case
            True -> pure $ Fix (void c)
            False -> local (S.insert $ void c) (go m w)

------------------------------------------------------------------------------
-- Exported Function
------------------------------------------------------------------------------

zonkVariableState :: Map KVar MonoKind -> VariableState -> VariableState
zonkVariableState m (VariableState lbs ubs tc k) = do
  let bisubst = (MkBisubstitution (M.empty, m) :: Bisubstitution UniVT)
  let zonkedlbs = zonk UniRep bisubst <$> lbs
  let zonkedubs = zonk UniRep bisubst <$> ubs
  let zonkedKind = zonkKind bisubst k
  VariableState zonkedlbs zonkedubs tc zonkedKind

-- | Creates the variable states that results from solving constraints.
solveConstraints :: ConstraintSet -> Map ModuleName Environment ->  Either (NE.NonEmpty Error) SolverResult
solveConstraints constraintSet@(ConstraintSet css _ _) env = do
  (_, solverState) <- runSolverM (solve ((Delay M.empty M.empty <$>) <$> css) >> runReaderT substitute S.empty) env (createInitState constraintSet)
  kvarSolution <- computeKVarSolution ErrorUnresolved (sst_kvars solverState)
  let tvarSol = zonkVariableState kvarSolution <$> sst_bounds solverState
  return $ MkSolverResult tvarSol kvarSolution
