module TypeInference.SolveConstraints
  ( solveConstraints
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Errors
import Syntax.Types
import Syntax.Kinds
import Syntax.CommonTerm (XtorName, FreeVarName)
import Syntax.Program (Environment)
import Pretty.Pretty
import Pretty.Types ()
import Pretty.Constraints ()
import TypeInference.GenerateConstraints.Definition ( InferenceMode(..) )

------------------------------------------------------------------------------
-- Constraint solver monad
------------------------------------------------------------------------------

data SolverState = SolverState
  { sst_bounds :: Map TVar VariableState
  , sst_kvars :: Map KVar Kind
  , sst_cache :: Set (Constraint ()) -- The constraints in the cache need to have their annotations removed!
  , sst_inferMode :: InferenceMode }

createInitState :: ConstraintSet -> InferenceMode -> SolverState
createInitState (ConstraintSet _ uvs _) im = SolverState { sst_bounds = M.fromList [(fst uv,emptyVarState) | uv <- uvs]
                                                         , sst_kvars = M.empty
                                                         , sst_cache = S.empty 
                                                         , sst_inferMode = im }

type SolverM a = (ReaderT (Environment, ()) (StateT SolverState (Except Error))) a

runSolverM :: SolverM a -> Environment -> SolverState -> Either Error (a, SolverState)
runSolverM m env initSt = runExcept (runStateT (runReaderT m (env,())) initSt)

------------------------------------------------------------------------------
-- Monadic helper functions
------------------------------------------------------------------------------

addToCache :: Constraint ConstraintInfo -> SolverM ()
addToCache cs = modifyCache (S.insert (const () <$> cs)) -- We delete the annotation when inserting into cache 
  where
    modifyCache :: (Set (Constraint ()) -> Set (Constraint ())) -> SolverM ()
    modifyCache f = modify (\(SolverState gr kvars cache im) -> SolverState gr kvars (f cache) im)

inCache :: Constraint ConstraintInfo -> SolverM Bool
inCache cs = gets sst_cache >>= \cache -> pure ((const () <$> cs) `elem` cache)

modifyBounds :: (VariableState -> VariableState) -> TVar -> SolverM ()
modifyBounds f uv = modify (\(SolverState varMap kvars cache im) -> SolverState (M.adjust f uv varMap) kvars cache im)

getBounds :: TVar -> SolverM VariableState
getBounds uv = do
  bounds <- gets sst_bounds
  case M.lookup uv bounds of
    Nothing -> throwSolverError [ "Tried to retrieve bounds for variable:"
                                , ppPrint uv
                                , "which is not a valid unification variable."
                                ]
    Just vs -> return vs

addUpperBound :: TVar -> Typ Neg -> SolverM [Constraint ConstraintInfo]
addUpperBound uv ty = do
  modifyBounds (\(VariableState ubs lbs) -> VariableState (ty:ubs) lbs)uv
  bounds <- getBounds uv
  let lbs = vst_lowerbounds bounds
  return [SubType UpperBoundConstraint lb ty | lb <- lbs]

addLowerBound :: TVar -> Typ Pos -> SolverM [Constraint ConstraintInfo]
addLowerBound uv ty = do
  modifyBounds (\(VariableState ubs lbs) -> VariableState ubs (ty:lbs)) uv
  bounds <- getBounds uv
  let ubs = vst_upperbounds bounds
  return [SubType LowerBoundConstraint ty ub | ub <- ubs]

------------------------------------------------------------------------------
-- Constraint solving algorithm
------------------------------------------------------------------------------

solve :: [Constraint ConstraintInfo] -> SolverM ()
solve [] = return ()
solve (cs:css) = do
  cacheHit <- inCache cs
  if cacheHit
    then solve css
    else do
      addToCache cs
      case cs of
        (KindEq k1 k2) -> do
          unifyKinds k1 k2
        (SubType _ (TyVar PosRep uv) ub) -> do
          newCss <- addUpperBound uv ub
          solve (newCss ++ css)
        (SubType _ lb (TyVar NegRep uv)) -> do
          newCss <- addLowerBound uv lb
          solve (newCss ++ css)
        _ -> do
          subCss <- subConstraints cs
          solve (subCss ++ css)

lookupXtor :: XtorName -> [XtorSig pol] -> SolverM (XtorSig pol)
lookupXtor xtName xtors = case find (\(MkXtorSig xtName' _) -> xtName == xtName') xtors of
  Nothing -> throwSolverError ["The xtor"
                              , ppPrint xtName
                              , "is not contained in the list of xtors"
                              , ppPrint xtors ]
  Just xtorSig -> pure xtorSig

checkXtor :: [XtorSig Neg] -> XtorSig Pos ->  SolverM [Constraint ConstraintInfo]
checkXtor xtors2 (MkXtorSig xtName (MkTypArgs prd1 cns1)) = do
  MkXtorSig _ (MkTypArgs prd2 cns2) <- lookupXtor xtName xtors2
  pure $ zipWith (SubType XtorSubConstraint) prd1 prd2 ++ zipWith (SubType XtorSubConstraint) cns2 cns1


unifyKinds :: Kind -> Kind -> SolverM ()
unifyKinds (MonoKind c1) (MonoKind c2) =
  if c1 == c2
    then return ()
    else throwSolverError [ "Cannot unify incompatible kinds: " <> ppPrint c1 <> " and " <> ppPrint c2]
unifyKinds (KindVar _kv) _k = return ()
unifyKinds _k (KindVar _kv) = return ()

-- | The `subConstraints` function takes a complex constraint, and decomposes it
-- into simpler constraints. A constraint is complex if it is not atomic. An atomic
-- constraint has a type variable on the right or left hand side of the constraint.
--
-- The `subConstraints` function is the function which will produce the error if the
-- constraint set generated from a program is not solvable.
subConstraints :: Constraint ConstraintInfo -> SolverM [Constraint ConstraintInfo]
-- Intersection and union constraints:
--
-- If the left hand side of the constraint is a intersection type, or the
-- right hand side is a union type, then the constraint can be directly decomposed
-- into structurally smaller subconstraints. E.g.:
--
--     ty1 \/ ty2 <: ty3         ~>     ty1 <: ty3   AND  ty2 <: ty3
--     ty1 <: ty2 /\ ty3         ~>     ty1 <: ty2   AND  ty1 <: ty3
--
subConstraints (SubType _ (TySet PosRep tys) ty) =
  return [SubType IntersectionUnionSubConstraint ty' ty | ty' <- tys]
subConstraints (SubType _ ty (TySet NegRep tys)) =
  return [SubType IntersectionUnionSubConstraint ty ty' | ty' <- tys]
-- Recursive constraints:
--
-- If the left hand side or the right hand side of the constraint is a recursive
-- mu-type, the mu-type gets unrolled once. Note that this case makes it non-obvious
-- that constraint generation is going to terminate. Examples:
--
--     rec a.ty1 <: ty2          ~>     ty1 [rec a.ty1 / a] <: ty2
--     ty1 <: rec a.ty2          ~>     ty1 <: ty2 [rec a.ty2 / a]
--
subConstraints (SubType _ ty@(TyRec _ _ _) ty') =
  return [SubType RecTypeSubConstraint (unfoldRecType ty) ty']
subConstraints (SubType _ ty' ty@(TyRec _ _ _)) =
  return [SubType RecTypeSubConstraint ty' (unfoldRecType ty)]
-- Constraints between structural data or codata types.
--
-- Constraints between structural data and codata types generates constraints based
-- on the xtors of the two types. In order to generate the constraints, the helper
-- function `checkXtors` is invoked.
--
--     < ctors1 > <: < ctors2 >  ~>     [ checkXtors ctors2 ctor | ctor <- ctors1 ]
--     { dtors1 } <: { dtors2 }  ~>     [ checkXtors dtors1 dtor | dtor <- dtors2 ]
--
subConstraints (SubType _ (TyData PosRep ctors1) (TyData NegRep ctors2)) = do
  constraints <- forM ctors1 (checkXtor ctors2)
  pure $ concat constraints
subConstraints (SubType _ (TyCodata PosRep dtors1) (TyCodata NegRep dtors2)) = do
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
subConstraints (SubType _ (TyNominal _ tn1) (TyNominal _ tn2)) =
  if tn1 == tn2 then pure [] else
    throwSolverError ["The following nominal types are incompatible:"
                     , "    " <> ppPrint tn1
                     , "and"
                     , "    " <> ppPrint tn2 ]
-- Constraints between refined types:
--
-- If left and right side refine the same nominal type, check if left side refinement is
-- subtype of right side refinement.
subConstraints (SubType ci t1@(TyRefined _ tn1 ty1) (TyRefined _ tn2 ty2)) =
  if tn1 == tn2 then return [SubType ci ty1 ty2] else
    throwSolverError ["The following refined types are incompatible:"
                     , "    " <> ppPrint t1
                     , "and"
                     , "    " <> ppPrint tn2 ]
-- Constraints between nominal and refined types:
--
-- Refinement types and nominal types are incomparable.
subConstraints (SubType _ t1@TyRefined{} t2@TyNominal{}) =
  throwSolverError ["The following types are incompatible:"
                        , "    " <> ppPrint t1
                        , "and"
                        , "    " <> ppPrint t2 ]
subConstraints (SubType _ t1@TyNominal{} t2@TyRefined{}) =
  throwSolverError ["The following types are incompatible:"
                   , "    " <> ppPrint t1
                   , "and"
                   , "    " <> ppPrint t2 ]
-- Constraints between structural data and codata types:
--
-- A constraint between a structural data type and a structural codata type
-- cannot be solved. E.g.:
--
--     < ctors > <: { dtors }    ~>     FAIL
--     { dtors } <: < ctors >    ~>     FAIL
--
subConstraints cs@(SubType _ (TyData _ _) (TyCodata _ _)) =
  throwSolverError [ "Constraint:"
                   , "     " <> ppPrint cs
                   , "is unsolvable. A data type can't be a subtype of a codata type!" ]
subConstraints cs@(SubType _ (TyCodata _ _) (TyData _ _)) =
  throwSolverError [ "Constraint:"
                   , "     " <> ppPrint cs
                   , "is unsolvable. A codata type can't be a subtype of a data type!" ]
-- Constraints between nominal and structural types:
--
-- These constraints cannot be solved. E.g.:
--
--     < ctors > <: Nat     ~>     FAIL
--     Nat <: < ctors >     ~>     FAIL
--
subConstraints (SubType _ t1@TyData{} t2@TyNominal{}) = do
  throwSolverError ["Cannot constrain structural type " <> ppPrint t1 <> " by nominal type " <> ppPrint t2]
subConstraints (SubType _ t1@TyCodata{} t2@TyNominal{}) = do
  throwSolverError ["Cannot constrain structural type " <> ppPrint t1 <> " by nominal type " <> ppPrint t2]
subConstraints (SubType _ t1@TyNominal{} t2@TyData{}) =
  throwSolverError ["Cannot constrain nominal type " <> ppPrint t1 <> " by structural type " <> ppPrint t2]
subConstraints (SubType _ t1@TyNominal{} t2@TyCodata{}) =
  throwSolverError ["Cannot constrain nominal type " <> ppPrint t1 <> " by structural type " <> ppPrint t2]
subConstraints (SubType _ t1@TyData{} t2@TyRefined{}) =
  throwSolverError ["Cannot constrain structural type " <> ppPrint t1 <> " by refinement type " <> ppPrint t2]
subConstraints (SubType _ t1@TyCodata{} t2@TyRefined{}) =
  throwSolverError ["Cannot constrain structural type " <> ppPrint t1 <> " by refinement type " <> ppPrint t2]
subConstraints (SubType _ t1@TyRefined{} t2@TyData{}) =
  throwSolverError ["Cannot constrain refinement type " <> ppPrint t1 <> " by structural type " <> ppPrint t2]
subConstraints (SubType _ t1@TyRefined{} t2@TyCodata{}) =
  throwSolverError ["Cannot constrain refinement type " <> ppPrint t1 <> " by structural type " <> ppPrint t2]
-- Atomic constraints:
--
-- Atomic constraints, i.e. constraints between a type and a type variable, should be
-- dealt with in the function `solve`. Calling the function `subConstraints` with an
-- atomic constraint is an implementation bug.
--
subConstraints (SubType _ ty1@(TyVar _ _) ty2) =
  throwSolverError ["subConstraints should only be called if neither upper nor lower bound are unification variables"
                   , ppPrint ty1
                   , "<:"
                   , ppPrint ty2
                   ]
subConstraints (SubType _ ty1 ty2@(TyVar _ _)) =
  throwSolverError ["subConstraints should only be called if neither upper nor lower bound are unification variables"
                   , ppPrint ty1
                   , "<:"
                   , ppPrint ty2
                   ]
subConstraints (KindEq _ _) =
  throwSolverError ["Unreachable"]

------------------------------------------------------------------------------
-- Exported Function
------------------------------------------------------------------------------

-- | Creates the variable states that results from solving constraints.
solveConstraints :: ConstraintSet -> Environment -> InferenceMode -> Either Error SolverResult
solveConstraints constraintSet@(ConstraintSet css _ _) env im = do
  (_, solverState) <- runSolverM (solve css) env (createInitState constraintSet im)
  return MkSolverResult { tvarSolution = sst_bounds solverState
                        , kvarSolution = sst_kvars solverState
                        }

