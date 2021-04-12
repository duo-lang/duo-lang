module TypeInference.SolveConstraints
  ( solveConstraints
  ) where

import Control.Monad.State
import Control.Monad.Except
import Data.List (find)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Syntax.Types
import Syntax.CommonTerm (XtorName)
import Utils
import Pretty.Pretty
import Pretty.Types ()
import Pretty.Constraints ()

------------------------------------------------------------------------------
-- Constraint solver monad
------------------------------------------------------------------------------

data SolverState = SolverState
  { sst_bounds :: SolverResult
  , sst_cache :: Set (Constraint ())}

createInitState :: ConstraintSet () -> SolverState
createInitState (ConstraintSet _ uvs) = SolverState { sst_bounds = M.fromList [(uv,emptyVarState) | uv <- uvs]
                                                    , sst_cache = S.empty }

type SolverM a = (StateT SolverState (Except Error)) a

runSolverM :: SolverM a -> SolverState -> Either Error (a, SolverState)
runSolverM m initSt = runExcept (runStateT m initSt)

------------------------------------------------------------------------------
-- Monadic helper functions
------------------------------------------------------------------------------

throwSolverError :: [String] -> SolverM a
throwSolverError = throwError . SolveConstraintsError . unlines

addToCache :: Constraint () -> SolverM ()
addToCache cs = modifyCache (S.insert cs)
  where
    modifyCache :: (Set (Constraint ()) -> Set (Constraint ())) -> SolverM ()
    modifyCache f = modify (\(SolverState gr cache) -> SolverState gr (f cache))

inCache :: Constraint () -> SolverM Bool
inCache cs = gets sst_cache >>= \cache -> pure (cs `elem` cache)

modifyBounds :: (VariableState -> VariableState) -> TVar -> SolverM ()
modifyBounds f uv = modify (\(SolverState varMap cache) -> SolverState (M.adjust f uv varMap) cache)

addUpperBound :: TVar -> Typ Neg -> SolverM [Constraint ()]
addUpperBound uv ty = do
  modifyBounds (\(VariableState ubs lbs) -> VariableState (ty:ubs) lbs)uv
  lbs <- gets (vst_lowerbounds . (M.! uv) . sst_bounds)
  return [SubType () lb ty | lb <- lbs]

addLowerBound :: TVar -> Typ Pos -> SolverM [Constraint ()]
addLowerBound uv ty = do
  modifyBounds (\(VariableState ubs lbs) -> VariableState ubs (ty:lbs)) uv
  ubs <- gets (vst_upperbounds . (M.! uv) . sst_bounds)
  return [SubType () ty ub | ub <- ubs]

------------------------------------------------------------------------------
-- Constraint solving algorithm
------------------------------------------------------------------------------

solve :: [Constraint ()] -> SolverM ()
solve [] = return ()
solve (cs:css) = do
  cacheHit <- inCache cs
  case cacheHit of
    True -> solve css
    False -> do
      addToCache cs
      case cs of
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

checkXtor :: [XtorSig Neg] -> XtorSig Pos ->  SolverM [Constraint ()]
checkXtor xtors2 (MkXtorSig xtName (MkTypArgs prd1 cns1)) = do
  MkXtorSig _ (MkTypArgs prd2 cns2) <- lookupXtor xtName xtors2
  pure $ zipWith (SubType ()) prd1 prd2 ++ zipWith (SubType ()) cns2 cns1

-- | The `subConstraints` function takes a complex constraint, and decomposes it
-- into simpler constraints. A constraint is complex if it is not atomic. An atomic
-- constraint has a type variable on the right or left hand side of the constraint.
--
-- The `subConstraints` function is the function which will produce the error if the
-- constraint set generated from a program is not solvable.
subConstraints :: Constraint () -> SolverM [Constraint ()]
-- Intersection and union constraints:
--
-- If the left hand side of the constraint is a intersection type, or the
-- right hand side is a union type, then the constraint can be directly decomposed
-- into structurally smaller subconstraints. E.g.:
--
--     ty1 /\ ty2 <: ty3         ~>     ty1 <: ty3   AND  ty2 <: ty3
--     ty1 <: ty2 \/ ty3         ~>     ty1 <: ty2   AND  ty1 <: ty3
--
subConstraints (SubType _ (TySet PosRep tys) ty) =
  return [SubType () ty' ty | ty' <- tys]
subConstraints (SubType _ ty (TySet NegRep tys)) =
  return [SubType () ty ty' | ty' <- tys]
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
  return [SubType () (unfoldRecType ty) ty']
subConstraints (SubType _ ty' ty@(TyRec _ _ _)) =
  return [SubType () ty' (unfoldRecType ty)]
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
-- We currently do not have any subtyping relationshipts between nominal types.
-- We therefore only have to check if the two nominal types are identical. E.g.:
--
--     Bool <: Nat               ~>     FAIL
--     Bool <: Bool              ~>     []
--
subConstraints (SubType _ (TyNominal _ tn1) (TyNominal _ tn2)) =
  case tn1 == tn2 of
    True  -> pure []
    False -> throwSolverError ["The following nominal types are incompatible:"
                              , "    " ++ ppPrint tn1
                              , "and"
                              , "    " ++ ppPrint tn2 ]
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
                   , "     " ++ ppPrint cs
                   , "is unsolvable. A data type can't be a subtype of a codata type!" ]
subConstraints cs@(SubType _ (TyCodata _ _) (TyData _ _)) =
  throwSolverError [ "Constraint:"
                   , "     " ++ ppPrint cs
                   , "is unsolvable. A codata type can't be a subtype of a data type!" ]
-- Constraints between nominal and a structural types:
--
-- These constraints are not solvable. E.g.:
--
--     < ctors > <: Nat          ~>     FAIL
--
subConstraints (SubType _ (TyData _ _) (TyNominal _ _)) =
  throwSolverError ["Cannot constrain nominal by structural type"]
subConstraints (SubType _ (TyCodata _ _) (TyNominal _ _)) =
  throwSolverError ["Cannot constrain nominal by structural type"]
subConstraints (SubType _ (TyNominal _ _) (TyData _ _)) =
  throwSolverError ["Cannot constrain nominal by structural type"]
subConstraints (SubType _ (TyNominal _ _) (TyCodata _ _)) =
  throwSolverError ["Cannot constrain nominal by structural type"]
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

------------------------------------------------------------------------------
-- Exported Function
------------------------------------------------------------------------------

-- | Creates the variable states that results from solving constraints.
solveConstraints :: ConstraintSet () -> Either Error SolverResult
solveConstraints constraintSet@(ConstraintSet css _) = do
  (_, solverState) <- runSolverM (solve css) (createInitState constraintSet)
  return (sst_bounds solverState)

