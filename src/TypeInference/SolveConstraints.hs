module TypeInference.SolveConstraints
  ( solveConstraints
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.List (find)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)
import Data.Set qualified as S

import Driver.Environment (Environment)
import Errors
import Syntax.Common.TypesPol
import Syntax.Common
import Pretty.Pretty
import Pretty.Types ()
import Pretty.Constraints ()
import TypeInference.Constraints

------------------------------------------------------------------------------
-- Constraint solver monad
------------------------------------------------------------------------------

data SolverState = SolverState
  { sst_bounds :: Map TVar VariableState
  , sst_cache :: Set (Constraint ()) -- The constraints in the cache need to have their annotations removed!
  }

createInitState :: ConstraintSet -> SolverState
createInitState (ConstraintSet _ uvs) = SolverState { sst_bounds = M.fromList [(fst uv,emptyVarState (error "createInitState: No Kind info available")) | uv <- uvs]
                                                       , sst_cache = S.empty
                                                       }


type SolverM a = (ReaderT (Map ModuleName Environment, ()) (StateT SolverState (Except Error))) a

runSolverM :: SolverM a -> Map ModuleName Environment -> SolverState -> Either Error (a, SolverState)
runSolverM m env initSt = runExcept (runStateT (runReaderT m (env,())) initSt)

------------------------------------------------------------------------------
-- Monadic helper functions
------------------------------------------------------------------------------

addToCache :: Constraint ConstraintInfo -> SolverM ()
addToCache cs = modifyCache (S.insert (() <$ cs)) -- We delete the annotation when inserting into cache
  where
    modifyCache :: (Set (Constraint ()) -> Set (Constraint ())) -> SolverM ()
    modifyCache f = modify (\(SolverState gr cache) -> SolverState gr (f cache))

inCache :: Constraint ConstraintInfo -> SolverM Bool
inCache cs = gets sst_cache >>= \cache -> pure ((() <$ cs) `elem` cache)

modifyBounds :: (VariableState -> VariableState) -> TVar -> SolverM ()
modifyBounds f uv = modify (\(SolverState varMap cache) -> SolverState (M.adjust f uv varMap) cache)

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
  modifyBounds (\(VariableState ubs lbs kind) -> VariableState (ty:ubs) lbs kind)uv
  bounds <- getBounds uv
  let lbs = vst_lowerbounds bounds
  return [SubType UpperBoundConstraint lb ty | lb <- lbs]

addLowerBound :: TVar -> Typ Pos -> SolverM [Constraint ConstraintInfo]
addLowerBound uv ty = do
  modifyBounds (\(VariableState ubs lbs kind) -> VariableState ubs (ty:lbs) kind) uv
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
  if cacheHit then solve css else (do
    addToCache cs
    case cs of
      (SubType _ (TyVar _ PosRep _ uv) ub) -> do
        newCss <- addUpperBound uv ub
        solve (newCss ++ css)
      (SubType _ lb (TyVar _ NegRep _ uv)) -> do
        newCss <- addLowerBound uv lb
        solve (newCss ++ css)
      _ -> do
        subCss <- subConstraints cs
        solve (subCss ++ css))

------------------------------------------------------------------------------
-- Computing Subconstraints
------------------------------------------------------------------------------

lookupXtor :: XtorName -> [XtorSig pol] -> SolverM (XtorSig pol)
lookupXtor xtName xtors = case find (\(MkXtorSig xtName' _) -> xtName == xtName') xtors of
  Nothing -> throwSolverError ["The xtor"
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
checkContexts (PrdCnsType PrdRep _:_) (PrdCnsType CnsRep _:_) = throwSolverError ["checkContexts: Tried to constrain PrdType by CnsType."]
checkContexts (PrdCnsType CnsRep _:_) (PrdCnsType PrdRep _:_) = throwSolverError ["checkContexts: Tried to constrain CnsType by PrdType."]
checkContexts []    (_:_) = throwSolverError ["checkContexts: Linear contexts have unequal length."]
checkContexts (_:_) []    = throwSolverError ["checkContexts: Linear contexts have unequal length."]


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
subConstraints (SubType _ (TyData _ PosRep Nothing ctors1) (TyData _ NegRep Nothing ctors2)) = do
  constraints <- forM ctors1 (checkXtor ctors2)
  pure $ concat constraints
subConstraints (SubType _ (TyCodata _ PosRep Nothing dtors1) (TyCodata _ NegRep Nothing dtors2)) = do
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
subConstraints (SubType _ t1@(TyData _ PosRep (Just tn1) ctors1) t2@(TyData _ NegRep (Just tn2) ctors2)) = do
  if tn1 == tn2 then do
    constraints <- forM ctors1 (checkXtor ctors2)
    pure $ concat constraints
  else throwSolverError ["The following refinement types are incompatible:"
                        , "    " <> ppPrint t1
                        , "and"
                        , "    " <> ppPrint t2 ]
subConstraints (SubType _ t1@(TyCodata _ PosRep (Just tn1) dtors1) t2@(TyCodata _ NegRep (Just tn2) dtors2)) = do
  if tn1 == tn2 then do
    constraints <- forM dtors2 (checkXtor dtors1)
    pure $ concat constraints
  else throwSolverError ["The following refinement types are incompatible:"
                        , "    " <> ppPrint t1
                        , "and"
                        , "    " <> ppPrint t2 ]
-- Constraints between structural (co)data types and refinement (co)data types:
--
-- These constraints are unsolvable. E.g.
--
--     < ctors > <: {{ TyName :>> < ctors > }}    ~>     FAIL
--     { dtors } <: {{ TyName :>> { dtors } }}    ~>     FAIL
--
subConstraints (SubType _ t1@(TyData _ PosRep (Just _) _) t2@(TyData _ NegRep Nothing _)) = do
  throwSolverError ["Cannot constraint refinement data type"
                   , "    " <> ppPrint t1
                   , "by structural data type"
                   , "    " <> ppPrint t2 ]
subConstraints (SubType _ t1@(TyData _ PosRep Nothing _) t2@(TyData _ NegRep (Just _) _)) = do
  throwSolverError ["Cannot constraint structural data type"
                   , "    " <> ppPrint t1
                   , "by refinement data type"
                   , "    " <> ppPrint t2 ]
subConstraints (SubType _ t1@(TyCodata _ PosRep (Just _) _) t2@(TyCodata _ NegRep Nothing _)) = do
  throwSolverError ["Cannot constraint refinement codata type"
                   , "    " <> ppPrint t1
                   , "by structural codata type"
                   , "    " <> ppPrint t2 ]
subConstraints (SubType _ t1@(TyCodata _ PosRep Nothing _) t2@(TyCodata _ NegRep (Just _) _)) = do
  throwSolverError ["Cannot constraint structural codata type"
                   , "    " <> ppPrint t1
                   , "by refinement codata type"
                   , "    " <> ppPrint t2 ]
-- Constraints between nominal types:
--
-- We currently do not have any subtyping relationships between nominal types.
-- We therefore only have to check if the two nominal types are identical. E.g.:
--
--     Bool <: Nat               ~>     FAIL
--     Bool <: Bool              ~>     []
--
subConstraints (SubType _ (TyNominal _ _ _ tn1 args1) (TyNominal _ _ _ tn2 args2)) =
  if tn1 == tn2 then do
    let f (CovariantType ty1) (CovariantType ty2) = SubType NominalSubConstraint ty1 ty2
        f (ContravariantType ty1) (ContravariantType ty2) = SubType NominalSubConstraint ty2 ty1
        f _ _ = error "cannot occur"
    pure (zipWith f args1 args2)
  else
    throwSolverError ["The following nominal types are incompatible:"
                     , "    " <> ppPrint tn1
                     , "and"
                     , "    " <> ppPrint tn2 ]
-- Constraints between structural data and codata types:
--
-- A constraint between a structural data type and a structural codata type
-- cannot be solved. E.g.:
--
--     < ctors > <: { dtors }    ~>     FAIL
--     { dtors } <: < ctors >    ~>     FAIL
--
subConstraints cs@(SubType _ TyData{} TyCodata{}) =
  throwSolverError [ "Constraint:"
                   , "     " <> ppPrint cs
                   , "is unsolvable. A data type can't be a subtype of a codata type!" ]
subConstraints cs@(SubType _ TyCodata{} TyData{}) =
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
-- Atomic constraints:
--
-- Atomic constraints, i.e. constraints between a type and a type variable, should be
-- dealt with in the function `solve`. Calling the function `subConstraints` with an
-- atomic constraint is an implementation bug.
--
subConstraints (SubType _ ty1@TyVar {} ty2) =
  throwSolverError ["subConstraints should only be called if neither upper nor lower bound are unification variables"
                   , ppPrint ty1
                   , "<:"
                   , ppPrint ty2
                   ]
subConstraints (SubType _ ty1 ty2@TyVar {}) =
  throwSolverError ["subConstraints should only be called if neither upper nor lower bound are unification variables"
                   , ppPrint ty1
                   , "<:"
                   , ppPrint ty2
                   ]
-- Primitive types:
subConstraints (SubType _ t1@(TyPrim _ _ pt1) t2@(TyPrim _ _ pt2)) =
  if pt1 == pt2 then do
    pure []
  else
    throwSolverError ["The following primitive types are incompatible:"
                     , "    " <> ppPrint t1
                     , "and"
                     , "    " <> ppPrint t2 ]
-- Constraints between primitive types and other types
--
-- These constraints cannot be solved.
subConstraints (SubType _ t1@TyPrim{} t2@TyNominal{}) = do
  throwSolverError ["Cannot constrain primitive type " <> ppPrint t1 <> " by nominal type " <> ppPrint t2]
subConstraints (SubType _ t1@TyNominal{} t2@TyPrim{}) = do
  throwSolverError ["Cannot constrain nominal type " <> ppPrint t1 <> " by primitive type " <> ppPrint t2]
subConstraints (SubType _ t1@TyPrim{} t2@TyData{}) = do
  throwSolverError ["Cannot constrain primitive type " <> ppPrint t1 <> " by structural type " <> ppPrint t2]
subConstraints (SubType _ t1@TyData{} t2@TyPrim{}) = do
  throwSolverError ["Cannot constrain structural type " <> ppPrint t1 <> " by primitive type " <> ppPrint t2]
subConstraints (SubType _ t1@TyPrim{} t2@TyCodata{}) = do
  throwSolverError ["Cannot constrain primitive type " <> ppPrint t1 <> " by structural type " <> ppPrint t2]
subConstraints (SubType _ t1@TyCodata{} t2@TyPrim{}) = do
  throwSolverError ["Cannot constrain structural type " <> ppPrint t1 <> " by primitive type " <> ppPrint t2]
subConstraints (SubType _ TyFlipPol {} _) = do
  throwSolverError ["Cannot compute subconstraints for TyFlipPol"]
subConstraints (SubType _ _ TyFlipPol {}) = do
  throwSolverError ["Cannot compute subconstraints for TyFlipPol"]
------------------------------------------------------------------------------
-- Exported Function
------------------------------------------------------------------------------

-- | Creates the variable states that results from solving constraints.
solveConstraints :: ConstraintSet -> Map ModuleName Environment ->  Either Error SolverResult
solveConstraints constraintSet@(ConstraintSet css _) env = do
  (_, solverState) <- runSolverM (solve css) env (createInitState constraintSet)
  pure (MkSolverResult (sst_bounds solverState))

