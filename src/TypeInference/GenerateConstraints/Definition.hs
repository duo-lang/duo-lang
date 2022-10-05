module TypeInference.GenerateConstraints.Definition
  ( -- Constraint Generation Monad
    GenM
  , GenerateReader(..)
  , GenConstraints(..)
  , runGenM
    -- Generating fresh unification variables
  , freshTVar
  , freshTVars
  , freshTVarsForTypeParams
  , paramsMap
  , createMethodSubst
    -- Throwing errors
  , throwGenError
    -- Looking up in context or environment
  , lookupContext
    -- Running computations in extended context or environment.
  , withContext
    -- Instantiating type schemes
  , instantiateTypeScheme
    -- Adding a constraint
  , addConstraint
    -- Other
  , PrdCnsToPol
  , foo
  , fromMaybeVar
  , prdCnsToPol
  , checkCorrectness
  , checkExhaustiveness
  , checkInstanceCoverage
  , GenerateState(..)
  , initialState
  , initialReader
) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.List.NonEmpty (NonEmpty)
import Data.Map ( Map )
import Data.Map qualified as M
import Data.Text qualified as T

import Driver.Environment
import Errors
import Lookup
import Syntax.RST.Types qualified as RST
import Syntax.TST.Types qualified as TST
import Syntax.CST.Names
import Syntax.CST.Kinds
import Syntax.CST.Types (PrdCnsRep(..), PrdCns(..))
import Syntax.RST.Types (Polarity(..), PolarityRep(..))
import Syntax.RST.Program as RST
import Syntax.TST.Program as TST
import TypeInference.Constraints
import Loc ( Loc, defaultLoc )
import Utils ( indexMaybe )

---------------------------------------------------------------------------------------------
-- GenerateState:
--
-- We use varCount for generating fresh type variables.
-- We collect all generated unification variables and constraints in a ConstraintSet.
---------------------------------------------------------------------------------------------
data GenerateState = GenerateState
  { uVarCount :: Int
  , kVarCount :: Int
  , constraintSet :: ConstraintSet
  , usedRecVars :: M.Map RecTVar MonoKind
  , usedSkolemVars :: M.Map SkolemTVar MonoKind
  , usedUniVars :: M.Map UniTVar MonoKind
  }

initialConstraintSet :: ConstraintSet
initialConstraintSet =
  ConstraintSet { cs_constraints = []
                , cs_uvars = []
                , cs_kvars = []
                }

initialState :: GenerateState
initialState = GenerateState {   uVarCount = 0
                               , constraintSet = initialConstraintSet
                               , kVarCount = 0
                               , usedRecVars = M.empty
                               , usedSkolemVars = M.empty
                               , usedUniVars = M.empty
                        }

---------------------------------------------------------------------------------------------
-- GenerateReader:
--
-- We have access to a program environment and a local variable context.
-- The context contains monotypes, whereas the environment contains type schemes.
---------------------------------------------------------------------------------------------

data GenerateReader = GenerateReader { context :: [TST.LinearContext Pos]
                                     , location :: Loc
                                     }

initialReader :: Loc -> Map ModuleName Environment -> (Map ModuleName Environment, GenerateReader)
initialReader loc env = (env, GenerateReader { context = [], location = loc })

---------------------------------------------------------------------------------------------
-- GenM
---------------------------------------------------------------------------------------------

newtype GenM a = GenM { getGenM :: ReaderT (Map ModuleName Environment, GenerateReader) (StateT GenerateState (ExceptT (NonEmpty Error) (Writer [Warning]))) a }
  deriving newtype (Functor, Applicative, Monad, MonadState GenerateState, MonadReader (Map ModuleName Environment, GenerateReader), MonadError (NonEmpty Error))

runGenM :: Loc -> Map ModuleName Environment -> GenM a -> (Either (NonEmpty Error) (a, ConstraintSet), [Warning])
runGenM loc env m = case runWriter (runExceptT (runStateT (runReaderT  (getGenM m) (initialReader loc env)) initialState)) of
  (Left err, warns) -> (Left err, warns)
  (Right (x, state),warns) -> (Right (x, constraintSet state), warns)

---------------------------------------------------------------------------------------------
-- A typeclass for generating constraints and transforming from a Core.X to a TST.X
---------------------------------------------------------------------------------------------

class GenConstraints a b | a -> b where
  genConstraints :: a -> GenM b

---------------------------------------------------------------------------------------------
-- Generating fresh unification variables
---------------------------------------------------------------------------------------------

freshTVar :: UVarProvenance -> Maybe MonoKind -> GenM (TST.Typ Pos, TST.Typ Neg)
freshTVar uvp kv = do
  uVarC <- gets uVarCount
  kVarC <- gets kVarCount
  uniVMap <- gets usedUniVars
  let tVar = MkUniTVar ("u" <> T.pack (show uVarC))
  let newKVar = MkKVar ("k" <> T.pack (show kVarC))
  let knd = case kv of Nothing -> KindVar newKVar; Just kv' -> kv'
  let inc = case kv of Nothing -> 1; Just _ -> 0;
  -- We need to increment the counter
  modify (\gs@GenerateState{} -> gs { uVarCount = uVarC + 1, kVarCount = kVarC + inc, usedUniVars = M.insert tVar knd uniVMap })
  -- We also need to add the uvar to the constraintset.
  modify (\gs@GenerateState{ constraintSet = cs@ConstraintSet { cs_uvars,cs_kvars } } ->
            gs { constraintSet = cs { cs_uvars = cs_uvars ++ [(tVar, uvp,knd)], cs_kvars = cs_kvars ++ case kv of Nothing -> [newKVar];Just _->[] } })
  return (TST.TyUniVar defaultLoc PosRep knd tVar, TST.TyUniVar defaultLoc NegRep knd tVar)

freshTVars :: [(PrdCns, Maybe FreeVarName, Maybe MonoKind)] -> GenM (TST.LinearContext Pos, TST.LinearContext Neg)
freshTVars [] = return ([],[])
freshTVars ((Prd,fv,mk):rest) = do
  (lctxtP, lctxtN) <- freshTVars rest
  (tp, tn) <- freshTVar (ProgramVariable (fromMaybeVar fv)) mk
  return (TST.PrdCnsType PrdRep tp:lctxtP, TST.PrdCnsType PrdRep tn:lctxtN)
freshTVars ((Cns,fv,kv):rest) = do
  (lctxtP, lctxtN) <- freshTVars rest
  (tp, tn) <- freshTVar (ProgramVariable (fromMaybeVar fv)) kv
  return (TST.PrdCnsType CnsRep tn:lctxtP, TST.PrdCnsType CnsRep tp:lctxtN)

freshTVarsForTypeParams :: forall pol. PolarityRep pol -> TST.DataDecl -> GenM ([TST.VariantType pol], TST.Bisubstitution TST.SkolemVT)
freshTVarsForTypeParams rep decl = 
  let MkPolyKind { kindArgs } = TST.data_kind decl
      tn = TST.data_name decl
  in do
    (varTypes, vars) <- freshTVars tn kindArgs
    let map = paramsMap kindArgs vars
    case rep of
      PosRep -> pure (varTypes, map)
      NegRep -> pure (varTypes, map)
  where
   freshTVars :: RnTypeName -> [(Variance, SkolemTVar, MonoKind)] -> GenM ([TST.VariantType pol],[(TST.Typ Pos, TST.Typ Neg)])
   freshTVars _ [] = pure ([],[])
   freshTVars tn ((variance,tv,mk) : vs) = do
    (vartypes,vs') <- freshTVars tn vs
    (tyPos, tyNeg) <- freshTVar (TypeParameter tn tv) (Just mk)
    case (variance, rep) of
      (Covariant, PosRep)     -> pure (TST.CovariantType tyPos     : vartypes, (tyPos, tyNeg) : vs')
      (Covariant, NegRep)     -> pure (TST.CovariantType tyNeg     : vartypes, (tyPos, tyNeg) : vs')
      (Contravariant, PosRep) -> pure (TST.ContravariantType tyNeg : vartypes, (tyPos, tyNeg) : vs')
      (Contravariant, NegRep) -> pure (TST.ContravariantType tyPos : vartypes, (tyPos, tyNeg) : vs')

createMethodSubst :: Loc -> ClassDeclaration -> GenM (TST.Bisubstitution TST.SkolemVT)
createMethodSubst loc decl = 
  let kindArgs = classdecl_kinds decl
      cn = classdecl_name decl
  in do
    vars <- freshTVars cn kindArgs
    pure $ paramsMap kindArgs vars
   where
   freshTVars ::  ClassName -> [(Variance,SkolemTVar, MonoKind)] -> GenM [(TST.Typ Pos, TST.Typ Neg)]
   freshTVars _ [] = pure []
   freshTVars cn ((variance,tv,mk) : vs) = do
    vs' <- freshTVars cn vs
    (tyPos, tyNeg) <- freshTVar (TypeClassInstance cn tv) (Just mk)
    addConstraint $ case variance of
       Covariant -> TypeClassPos (InstanceConstraint loc) cn tyPos
       Contravariant -> TypeClassPos (InstanceConstraint loc) cn tyPos
    pure ((tyPos, tyNeg) : vs')

paramsMap :: [(Variance, SkolemTVar, MonoKind)]-> [(TST.Typ Pos, TST.Typ Neg)] -> TST.Bisubstitution TST.SkolemVT
paramsMap kindArgs freshVars =
  TST.MkBisubstitution (M.fromList (zip ((\(_,tv,_) -> tv) <$> kindArgs) freshVars))

---------------------------------------------------------------------------------------------
-- Running computations in an extended context or environment
---------------------------------------------------------------------------------------------

withContext :: TST.LinearContext 'Pos -> GenM a -> GenM a
withContext ctx = local (\(env,gr@GenerateReader{..}) -> (env, gr { context = ctx:context }))

---------------------------------------------------------------------------------------------
-- Looking up types in the context and environment
---------------------------------------------------------------------------------------------

-- | Lookup a type of a bound variable in the context.
lookupContext :: Loc -> PrdCnsRep pc -> Index -> GenM (TST.Typ (PrdCnsToPol pc))
lookupContext loc rep idx@(i,j) = do
  let rep' = case rep of PrdRep -> Prd; CnsRep -> Cns
  ctx <- asks (context . snd)
  case indexMaybe ctx i of
    Nothing -> throwGenError (BoundVariableOutOfBounds loc rep' idx)
    Just lctxt -> case indexMaybe lctxt j of
      Nothing -> throwGenError (BoundVariableOutOfBounds loc rep' idx)
      Just ty -> case (rep, ty) of
        (PrdRep, TST.PrdCnsType PrdRep ty) -> return ty
        (CnsRep, TST.PrdCnsType CnsRep ty) -> return ty
        (PrdRep, TST.PrdCnsType CnsRep _) -> throwGenError (BoundVariableWrongMode loc rep' idx)
        (CnsRep, TST.PrdCnsType PrdRep _) -> throwGenError (BoundVariableWrongMode loc rep' idx)


---------------------------------------------------------------------------------------------
-- Instantiating type schemes with fresh unification variables.
---------------------------------------------------------------------------------------------
--
instantiateTypeScheme :: FreeVarName -> Loc -> TST.TypeScheme pol -> GenM (TST.Typ pol)
instantiateTypeScheme fv loc TST.TypeScheme { ts_vars, ts_monotype } = do
  freshVars <- forM ts_vars (\tv -> freshTVar (TypeSchemeInstance fv loc) Nothing >>= \ty -> return (tv, ty))
  forM_ freshVars (\(_,ty) -> addConstraint (KindEq  KindConstraint (TST.getKind ts_monotype) (TST.getKind $ fst ty)))
  forM_ freshVars (\(_,ty) -> addConstraint (KindEq  KindConstraint (TST.getKind ts_monotype) (TST.getKind $ snd ty)))
  pure $ TST.zonk TST.SkolemRep (TST.MkBisubstitution (M.fromList freshVars)) ts_monotype

---------------------------------------------------------------------------------------------
-- Adding a constraint
---------------------------------------------------------------------------------------------

-- | Add a constraint to the state.
addConstraint :: Constraint ConstraintInfo -> GenM ()
addConstraint c = modify foo
  where
    foo gs@GenerateState { constraintSet } = gs { constraintSet = bar constraintSet }
    bar cs@ConstraintSet { cs_constraints } = cs { cs_constraints = c:cs_constraints }


---------------------------------------------------------------------------------------------
-- Other
---------------------------------------------------------------------------------------------

-- | Specifies whether to infer nominal or refined types
data InferenceMode = InferNominal | InferRefined
  deriving (Eq, Show)

foo :: PrdCnsRep pc -> PolarityRep (PrdCnsToPol pc)
foo PrdRep = PosRep
foo CnsRep = NegRep

fromMaybeVar :: Maybe FreeVarName -> FreeVarName
fromMaybeVar Nothing = MkFreeVarName "generated"
fromMaybeVar (Just fv) = fv

-- | Checks for a given list of XtorNames and a type declaration whether all the xtor names occur in
-- the type declaration (Correctness).
checkCorrectness :: Loc 
                 -> [XtorName]
                 -> TST.DataDecl
                 -> GenM ()
checkCorrectness loc matched decl = do
  let declared = TST.sig_name <$> fst (TST.data_xtors decl)
  forM_ matched $ \xn -> unless (xn `elem` declared)
    (throwGenError (PatternMatchAdditional loc xn (TST.data_name decl)))

-- | Checks for a given list of XtorNames and a type declaration whether all xtors of the type declaration
-- are matched against (Exhaustiveness).
checkExhaustiveness :: Loc
                    -> [XtorName] -- ^ The xtor names used in the pattern match
                    -> TST.DataDecl   -- ^ The type declaration to check against.
                    -> GenM ()
checkExhaustiveness loc matched decl = do
  let declared = TST.sig_name <$> fst (TST.data_xtors decl)
  forM_ declared $ \xn -> unless (xn `elem` matched)
    (throwGenError (PatternMatchMissingXtor loc xn (TST.data_name decl)))

-- | Check well-definedness of an instance, i.e. every method specified in the class declaration is implemented
-- in the instance declaration and every implemented method is actually declared.
checkInstanceCoverage :: Loc
                      -> RST.ClassDeclaration -- ^ The class declaration to check against.
                      -> [MethodName]         -- ^ The methods implemented in the instance.
                      -> GenM ()
checkInstanceCoverage loc RST.MkClassDeclaration { classdecl_methods } instanceMethods = do
  let classMethods = RST.msig_name <$> fst classdecl_methods
  forM_ classMethods $ \m -> unless (m `elem` instanceMethods)
    (throwGenError (InstanceImplementationMissing loc m))
  forM_ instanceMethods $ \m -> unless (m `elem` classMethods)
    (throwGenError (InstanceImplementationAdditional loc m))
