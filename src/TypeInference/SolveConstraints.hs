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
--import Data.Text qualified as T
import Data.List (partition)
import Data.Maybe (fromJust, isJust)
import Data.Bifunctor (second)

import Driver.Environment (Environment (..))
import Errors
import Syntax.TST.Types
import Syntax.RST.Types (PolarityRep(..), Polarity(..))
import Pretty.Pretty
import Pretty.Types ()
import Pretty.Constraints ()
import TypeInference.Constraints
import Loc ( defaultLoc, getLoc )
import Syntax.CST.Names
import Syntax.CST.Types ( PrdCnsRep(..))
import Syntax.CST.Kinds
import Syntax.TST.Program (InstanceDeclaration)
import Utils (nestedLookup)

------------------------------------------------------------------------------
-- Constraint solver monad
------------------------------------------------------------------------------

data SolverState = SolverState
  { sst_bounds :: Map UniTVar VariableState
  , sst_cache :: Set (Constraint ()) -- The constraints in the cache need to have their annotations removed!
  , sst_kvars :: [([KVar], Maybe MonoKind)]
  }

createInitState :: ConstraintSet -> SolverState
createInitState (ConstraintSet _ uvs kuvs) =
  SolverState { sst_bounds =  M.fromList [(fst uv,emptyVarState (KindVar (MkKVar "TODO"))) | uv <- uvs]
              , sst_cache = S.empty
              , sst_kvars = [([kv],Nothing) | kv <- kuvs]
              }


type SolverM a = (ReaderT (Map ModuleName Environment, ()) (StateT SolverState (Except (NE.NonEmpty Error)))) a

runSolverM :: SolverM a -> Map ModuleName Environment -> SolverState -> Either (NE.NonEmpty Error) (a, SolverState)
runSolverM m env initSt = runExcept (runStateT (runReaderT m (env,())) initSt)

------------------------------------------------------------------------------
-- Monadic helper functions
------------------------------------------------------------------------------

addToCache :: Constraint ConstraintInfo -> SolverM ()
addToCache cs = modifyCache (S.insert (() <$ cs)) -- We delete the annotation when inserting into cache
  where
    modifyCache :: (Set (Constraint ()) -> Set (Constraint ())) -> SolverM ()
    modifyCache f = modify (\(SolverState gr cache kvars) -> SolverState gr (f cache) kvars)

inCache :: Constraint ConstraintInfo -> SolverM Bool
inCache cs = gets sst_cache >>= \cache -> pure ((() <$ cs) `elem` cache)

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

addUpperBound :: UniTVar -> Typ Neg -> SolverM [Constraint ConstraintInfo]
addUpperBound uv ty = do
  modifyBounds (\(VariableState ubs lbs poscns negcns kind) -> VariableState (ty:ubs) lbs poscns negcns kind) uv
  bounds <- getBounds uv
  let lbs = vst_lowerbounds bounds
  return [SubType UpperBoundConstraint lb ty | lb <- lbs]

addLowerBound :: UniTVar -> Typ Pos -> SolverM [Constraint ConstraintInfo]
addLowerBound uv ty = do
  modifyBounds (\(VariableState ubs lbs poscns negcns kind) -> VariableState ubs (ty:lbs) poscns negcns kind) uv
  bounds <- getBounds uv
  let ubs = vst_upperbounds bounds
  return [SubType LowerBoundConstraint ty ub | ub <- ubs]

-- | Add and propagate type class constraints (might be superfluous).
addTypeClassConstraint :: PolarityRep pol -> UniTVar -> ClassName -> SolverM [Constraint ConstraintInfo]
addTypeClassConstraint PosRep uv cn = do
  modifyBounds (\(VariableState ubs lbs poscns negcns kind) -> VariableState ubs lbs (cn:poscns) negcns kind) uv
  bounds <- getBounds uv
  let lbs = vst_lowerbounds bounds
  return [TypeClassPos (TypeClassConstraint defaultLoc) cn lb | lb <- lbs]
addTypeClassConstraint NegRep uv cn = do
  modifyBounds (\(VariableState ubs lbs poscns negcns kind) -> VariableState ubs lbs poscns (cn:negcns) kind) uv
  bounds <- getBounds uv
  let ubs = vst_upperbounds bounds
  return [TypeClassNeg (TypeClassConstraint defaultLoc) cn ub | ub <- ubs]

-- lookupKVar :: KVar -> Map (Maybe MonoKind) (Set KVar) -> SolverM (Maybe MonoKind, Set KVar)
-- lookupKVar kv mp = case M.toList (M.filter (\x -> kv `elem` x) mp) of 
--   [] -> throwSolverError defaultLoc ["Kind variable not found."]
--   [(mk,set)] -> pure (mk,set)
--   _ -> throwSolverError defaultLoc ["Multiple kinds for kind variable" <> T.pack (show kv)]

------------------------------------------------------------------------------
-- Constraint solving algorithm
------------------------------------------------------------------------------

solve :: [Constraint ConstraintInfo] -> SolverM ()
solve [] = return ()
solve (cs:css) = do
  cacheHit <- inCache cs
  if cacheHit then solve css else (do
    addToCache cs
    case cs of
      (KindEq _ k1 k2) -> do
        unifyKinds k1 k2
        solve css
      (SubType _ (TyUniVar _ PosRep _ uvl) tvu@(TyUniVar _ NegRep _ uvu)) ->
        if uvl == uvu
        then solve css
        else do
          newCss <- addUpperBound uvl tvu
          solve (newCss ++ css)
      (SubType _ (TyUniVar _ PosRep _ uv) ub) -> do
        newCss <- addUpperBound uv ub
        solve (newCss ++ css)
      (SubType _ lb (TyUniVar _ NegRep _ uv)) -> do
        newCss <- addLowerBound uv lb
        solve (newCss ++ css)
      (TypeClassPos _ cn (TyUniVar _ PosRep _ uv)) -> do
        addTypeClassConstraint PosRep uv cn
        solve css
      (TypeClassNeg _ cn (TyUniVar _ NegRep _ uv)) -> do
        addTypeClassConstraint NegRep uv cn
        solve css
      _ -> do
        subCss <- subConstraints cs
        solve (subCss ++ css))

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
      (Nothing, mk2) -> putKVars $ (newSet,mk2):rest1
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
unifyKinds _ _ = throwSolverError defaultLoc ["Not implemented"]

computeKVarSolution :: KindPolicy -> [([KVar],Maybe MonoKind)] -> Either (NE.NonEmpty Error) (Map KVar MonoKind)
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

checkXtor :: [XtorSig Neg] -> XtorSig Pos ->  SolverM [Constraint ConstraintInfo]
checkXtor xtors2 (MkXtorSig xtName subst1) = do
  MkXtorSig _ subst2 <- lookupXtor xtName xtors2
  checkContexts subst1 subst2

checkContexts :: LinearContext Pos -> LinearContext Neg -> SolverM [Constraint ConstraintInfo]
checkContexts [] [] = return []
checkContexts (PrdCnsType PrdRep ty1:rest1) (PrdCnsType PrdRep ty2:rest2) = do
  xs <- checkContexts rest1 rest2
  return (SubType XtorSubConstraint ty1 ty2:xs)
checkContexts (PrdCnsType CnsRep ty1:rest1) (PrdCnsType CnsRep ty2:rest2) = do
  xs <- checkContexts rest1 rest2
  return (SubType XtorSubConstraint ty2 ty1:xs)
checkContexts (PrdCnsType PrdRep _:_) (PrdCnsType CnsRep _:_) =
  throwSolverError defaultLoc ["checkContexts: Tried to constrain PrdType by CnsType."]
checkContexts (PrdCnsType CnsRep _:_) (PrdCnsType PrdRep _:_) =
  throwSolverError defaultLoc ["checkContexts: Tried to constrain CnsType by PrdType."]
checkContexts []    (_:_) =
  throwSolverError defaultLoc ["checkContexts: Linear contexts have unequal length."]
checkContexts (_:_) []    =
  throwSolverError defaultLoc ["checkContexts: Linear contexts have unequal length."]


-- | The `subConstraints` function takes a complex constraint, and decomposes it
-- into simpler constraints. A constraint is complex if it is not atomic. An atomic
-- constraint has a type variable on the right or left hand side of the constraint.
--
-- The `subConstraints` function is the function which will produce the error if the
-- constraint set generated from a program is not solvable.
subConstraints :: Constraint ConstraintInfo -> SolverM [Constraint ConstraintInfo]
-- Type synonyms are unfolded and are not preserved through constraint solving.
-- A more efficient solution to directly compare type synonyms is possible in the
-- future.
subConstraints (SubType annot (TySyn _ _ _ ty) ty') =
  pure [SubType annot ty ty']
subConstraints (SubType annot ty (TySyn _ _ _ ty')) =
  pure [SubType annot ty ty']
-- Intersection and union constraints:
--
-- If the left hand side of the constraint is a intersection type, or the
-- right hand side is a union type, then the constraint can be directly decomposed
-- into structurally smaller subconstraints. E.g.:
--
--     ty1 \/ ty2 <: ty3         ~>     ty1 <: ty3   AND  ty2 <: ty3
--     ty1 <: ty2 /\ ty3         ~>     ty1 <: ty2   AND  ty1 <: ty3
--
subConstraints (SubType _ _ (TyTop _ _)) =
  pure []
subConstraints (SubType _ (TyBot _ _) _) =
  pure []
subConstraints (SubType _ (TyUnion _ _ ty1 ty2) ty3) =
  pure [ SubType IntersectionUnionSubConstraint ty1 ty3
       , SubType IntersectionUnionSubConstraint ty2 ty3
       ]
subConstraints (SubType _ ty1 (TyInter _ _ ty2 ty3)) =
  pure [ SubType IntersectionUnionSubConstraint ty1 ty2
       , SubType IntersectionUnionSubConstraint ty1 ty3
       ]
-- Recursive constraints:
--
-- If the left hand side or the right hand side of the constraint is a recursive
-- mu-type, the mu-type gets unrolled once. Note that this case makes it non-obvious
-- that constraint generation is going to terminate. Examples:
--
--     rec a.ty1 <: ty2          ~>     ty1 [rec a.ty1 / a] <: ty2
--     ty1 <: rec a.ty2          ~>     ty1 <: ty2 [rec a.ty2 / a]
--
subConstraints (SubType _ ty@TyRec{} ty') =
  return [SubType RecTypeSubConstraint (unfoldRecType ty) ty']
subConstraints (SubType _ ty' ty@TyRec{}) =
  return [SubType RecTypeSubConstraint ty' (unfoldRecType ty)]
-- Constraints between structural data or codata types:
--
-- Constraints between structural data and codata types generate constraints based
-- on the xtors of the two types. In order to generate the constraints, the helper
-- function `checkXtors` is invoked.
--
--     < ctors1 > <: < ctors2 >  ~>     [ checkXtors ctors2 ctor | ctor <- ctors1 ]
--     { dtors1 } <: { dtors2 }  ~>     [ checkXtors dtors1 dtor | dtor <- dtors2 ]
--
subConstraints (SubType _ (TyData _ PosRep _ ctors1) (TyData _ NegRep _ ctors2)) = do
  constraints <- forM ctors1 (checkXtor ctors2)
  pure $ concat constraints

subConstraints (SubType _ (TyCodata _ PosRep _ dtors1) (TyCodata _ NegRep _ dtors2)) = do
  constraints <- forM dtors2 (checkXtor dtors1)
  pure $ concat constraints

-- Constraints between refinement data or codata types:
--
-- These constraints are treated in the same way as those between structural (co)data types, with
-- the added condition that the type names must match. E.g.
--
--     {{ Nat :>> < ctors1 > }} <: {{ Nat  :>> < ctors2 > }}   ~>    [ checkXtors ctors2 ctor | ctor <- ctors1 ]
--     {{ Nat :>> < ctors1 > }} <: {{ Bool :>> < ctors2 > }}   ~>    FAIL
--
subConstraints (SubType _ (TyDataRefined _ PosRep _ tn1 ctors1) (TyDataRefined _ NegRep _ tn2 ctors2)) | tn1 == tn2 = do
  constraints <- forM ctors1 (checkXtor ctors2)
  pure $ concat constraints

subConstraints (SubType _ (TyCodataRefined _ PosRep _ tn1 dtors1) (TyCodataRefined _ NegRep _ tn2 dtors2))  | tn1 == tn2 = do
  constraints <- forM dtors2 (checkXtor dtors1)
  pure $ concat constraints

-- Constraints between nominal types:
--
-- We currently do not have any subtyping relationships between nominal types.
-- We therefore only have to check if the two nominal types are identical. E.g.:
--
--     Bool <: Nat               ~>     FAIL
--     Bool <: Bool              ~>     []
--
subConstraints (SubType _ (TyNominal _ _ _ tn1 args1) (TyNominal _ _ _ tn2 args2)) | tn1 == tn2 = do
    let f (CovariantType ty1) (CovariantType ty2) = SubType NominalSubConstraint ty1 ty2
        f (ContravariantType ty1) (ContravariantType ty2) = SubType NominalSubConstraint ty2 ty1
        f _ _ = error "cannot occur"
    pure (zipWith f args1 args2)
-- Constraints between primitive types:
subConstraints (SubType _ (TyI64 _ _) (TyI64 _ _)) = pure []
subConstraints (SubType _ (TyF64 _ _) (TyF64 _ _)) = pure []
subConstraints (SubType _ (TyChar _ _) (TyChar _ _)) = pure []
subConstraints (SubType _ (TyString _ _) (TyString _ _)) = pure []
-- All other constraints cannot be solved.
subConstraints (SubType _ t1 t2) = do
  throwSolverError defaultLoc ["Cannot constraint type"
                              , "    " <> ppPrint t1
                              , "by type"
                              , "    " <> ppPrint t2 ]
-- subConstraints for type classes are deprecated
-- type class constraints should only be resolved after subtype constraints
subConstraints (TypeClassPos _ _cn _typ) = pure []
subConstraints (TypeClassNeg _ _cn _tyn) = pure []
subConstraints KindEq{} = throwSolverError defaultLoc ["subContraints should not be called on Kind Equality Constraints"]

------------------------------------------------------------------------------
-- Instance Resolution
------------------------------------------------------------------------------

isAtomicType :: Typ pol -> Maybe (Typ pol)
isAtomicType t@TySkolemVar {} = Just t
isAtomicType t@TyUniVar {} = Just t
isAtomicType t@TyRecVar {} = Just t
isAtomicType t@TyData {} = Just t
isAtomicType t@TyCodata {} = Just t
isAtomicType t@TyDataRefined {} = Just t
isAtomicType t@TyCodataRefined {} = Just t
isAtomicType t@TyNominal {} = Just t
isAtomicType _ = Nothing

solveClassConstraints :: UniTVar -> VariableState -> SolverM (Map ClassName ())
solveClassConstraints uvar VariableState { vst_upperbounds, vst_lowerbounds, vst_posclasses, vst_negclasses } = do
  _ <- solveCoClasses vst_upperbounds vst_posclasses
  _ <- solveContraClasses vst_lowerbounds vst_negclasses
  pure M.empty

solveCoClasses :: [Typ Neg] -> [ClassName] -> SolverM (Map ClassName ())
solveCoClasses = undefined

solveCoClass :: Typ Neg -> ClassName -> SolverM (ModuleName, InstanceDeclaration)
-- from rules:
solveCoClass t@TyTop {} cn = throwSolverError (getLoc t) [ "Cannot find instance " <> ppPrint cn
                                                         , "for top type." ]
solveCoClass (TyInter _ _ t1 t2) cn =
  catchError (solveCoClass t1 cn) (const $ solveCoClass t2 cn)
-- atomic:
solveCoClass (isAtomicType -> Just t) cn = getInstanceNeg cn t
-- rest:
solveCoClass t cn = throwSolverError (getLoc t) [ "Cannot find instance " <> ppPrint cn
                                                , "for positive type " <> ppPrint t ]

solveContraClasses :: [Typ Pos] -> [ClassName] -> SolverM (Map ClassName ())
solveContraClasses = undefined

solveContraClass :: Typ Pos -> ClassName -> SolverM (ModuleName, InstanceDeclaration)
-- from rules:
solveContraClass t@TyBot {} cn = throwSolverError (getLoc t) [ "Cannot find instance " <> ppPrint cn

                                                             , "for bot type." ]
solveContraClass (TyUnion _ _ t1 t2) cn =
  catchError (solveContraClass t1 cn) (const $ solveContraClass t2 cn)
-- atomic:
solveContraClass (isAtomicType -> Just t) cn = getInstancePos cn t
-- rest:
solveContraClass t cn = throwSolverError (getLoc t) [ "Cannot find instance " <> ppPrint cn
                                                    , "for negative type " <> ppPrint t ]

getInstancePos :: ClassName -> Typ Pos -> SolverM (ModuleName, InstanceDeclaration)
getInstancePos cn typ = do
   (envMap,()) <- ask
   case nestedLookup (cn,typ) (M.map instancePosEnv envMap) of
     Nothing -> throwSolverError (getLoc typ) [ "Cannot find instance " <> ppPrint cn
                                              , "for positive type " <> ppPrint typ ]
     (Just idecl) -> pure idecl

getInstanceNeg :: ClassName -> Typ Neg -> SolverM (ModuleName, InstanceDeclaration)
getInstanceNeg cn typ = do
  (envMap,()) <- ask
  case nestedLookup (cn,typ) (M.map instanceNegEnv envMap) of
    Nothing -> throwSolverError (getLoc typ) [ "Cannot find instance " <> ppPrint cn
                                             , "for negative type " <> ppPrint typ ]
    (Just idecl) -> pure idecl

------------------------------------------------------------------------------
-- Exported Function
------------------------------------------------------------------------------

zonkVariableState :: Map KVar MonoKind -> VariableState -> VariableState
zonkVariableState m (VariableState lbs ubs pc nc k) = do
  let bisubst = (MkBisubstitution (M.empty, m) :: Bisubstitution UniVT)
  let zonkedlbs = zonk UniRep bisubst <$> lbs
  let zonkedubs = zonk UniRep bisubst <$> ubs
  let zonkedKind = zonkKind bisubst k
  VariableState zonkedlbs zonkedubs pc nc zonkedKind

-- | Creates the variable states that results from solving constraints.
solveConstraints :: ConstraintSet -> Map ModuleName Environment ->  Either (NE.NonEmpty Error) SolverResult
solveConstraints constraintSet@(ConstraintSet css _ _) env = do
  (_, solverState) <- runSolverM (solve css) env (createInitState constraintSet)
  kvarSolution <- computeKVarSolution DefaultCBV (sst_kvars solverState)
  let tvarSol = zonkVariableState kvarSolution <$> sst_bounds solverState
  return $ MkSolverResult tvarSol kvarSolution
