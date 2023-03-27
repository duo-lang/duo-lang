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
  , replaceUniVars
  , paramsMap
  , createMethodSubst
  , insertSkolemsClass
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
import Data.List.NonEmpty qualified as NE 

import TypeInference.Environment
import Errors
import Errors.Renamer
import Syntax.RST.Types qualified as RST
import Syntax.TST.Types qualified as TST
import Syntax.CST.Names
import Syntax.CST.Kinds
import Syntax.CST.Types (PrdCnsRep(..), PrdCns(..))
import Syntax.RST.Types (Polarity(..), PolarityRep(..))
import Syntax.RST.Program as RST
import Syntax.RST.Names
import Syntax.RST.Kinds
import Syntax.TST.Program as TST
import Syntax.LocallyNameless (Index)
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
  , usedRecVars :: M.Map RecTVar PolyKind
  , usedSkolemVars :: M.Map SkolemTVar PolyKind
  , usedUniVars :: M.Map UniTVar AnyKind
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
runGenM loc env m = case runWriter (runExceptT (runStateT (runReaderT  m.getGenM (initialReader loc env)) initialState)) of
  (Left err, warns) -> (Left err, warns)
  (Right (x, state),warns) -> (Right (x, state.constraintSet), warns)

---------------------------------------------------------------------------------------------
-- A typeclass for generating constraints and transforming from a Core.X to a TST.X
---------------------------------------------------------------------------------------------

class GenConstraints a b | a -> b where
  genConstraints :: a -> GenM b

---------------------------------------------------------------------------------------------
-- Generating fresh unification variables
---------------------------------------------------------------------------------------------

freshTVar :: UVarProvenance -> Maybe AnyKind -> GenM (TST.Typ Pos, TST.Typ Neg)
freshTVar uvp Nothing = do
  uVarC <- gets (\x -> x.uVarCount)
  kVarC <- gets (\x -> x.kVarCount)
  uniMap <- gets (\x -> x.usedUniVars)
  let tVar = MkUniTVar ("u" <> T.pack (show uVarC))
  let kVar = MkKVar ("k" <> T.pack (show kVarC))
  modify (\gs -> 
    gs {uVarCount = uVarC+1, kVarCount = kVarC+1, usedUniVars = M.insert tVar (MkPknd $ KindVar kVar) uniMap,  
        constraintSet = gs.constraintSet {cs_uvars = (tVar, uvp, MkPknd $ KindVar kVar) : gs.constraintSet.cs_uvars, cs_kvars = kVar : gs.constraintSet.cs_kvars}})
  return (TST.TyUniVar defaultLoc PosRep (MkPknd $ KindVar kVar) tVar, TST.TyUniVar defaultLoc NegRep (MkPknd $ KindVar kVar) tVar)
freshTVar uvp (Just pk) = do
  uVarC <- gets (\x -> x.uVarCount)
  uniMap <- gets (\x -> x.usedUniVars)
  let tVar = MkUniTVar ("u" <> T.pack (show uVarC))
  modify (\gs-> 
    gs {uVarCount = uVarC+1, usedUniVars = M.insert tVar pk uniMap, constraintSet = gs.constraintSet {cs_uvars = (tVar, uvp,pk) : gs.constraintSet.cs_uvars}})
  return (TST.TyUniVar defaultLoc PosRep pk tVar, TST.TyUniVar defaultLoc NegRep pk tVar)

freshTVars :: [(PrdCns, Maybe FreeVarName, AnyKind)] -> GenM (TST.LinearContext Pos, TST.LinearContext Neg)
freshTVars [] = return ([],[])
freshTVars ((Prd,fv,knd):rest) = do
  (lctxtP, lctxtN) <- freshTVars rest
  (tp, tn) <- freshTVar (ProgramVariable (fromMaybeVar fv)) (Just knd)
  return (TST.PrdCnsType PrdRep tp:lctxtP, TST.PrdCnsType PrdRep tn:lctxtN)
freshTVars ((Cns,fv,knd):rest) = do
  (lctxtP, lctxtN) <- freshTVars rest
  (tp, tn) <- freshTVar (ProgramVariable (fromMaybeVar fv)) (Just knd)
  return (TST.PrdCnsType CnsRep tn:lctxtP, TST.PrdCnsType CnsRep tp:lctxtN)

freshTVarsForTypeParams :: forall pol. PolarityRep pol -> TST.DataDecl -> GenM ([TST.VariantType pol], TST.Bisubstitution TST.SkolemVT)
freshTVarsForTypeParams rep decl = do
  kindArgs <- case decl.data_kind of
                    knd@MkPolyKind {} -> pure knd.kindArgs
                    k -> throwOtherError decl.data_loc [ "Wrong kind for data declaration: expected polykind, found " <> T.pack (show k) ]
  let tn = decl.data_name
  (varTypes, vars) <- freshTVars tn kindArgs
  let map = paramsMap kindArgs vars
  case rep of
    PosRep -> pure (varTypes, map)
    NegRep -> pure (varTypes, map)
  where
   freshTVars :: RnTypeName -> [(Variance, SkolemTVar, MonoKind)] -> GenM ([TST.VariantType pol],[(TST.Typ Pos, TST.Typ Neg)])
   freshTVars _ [] = pure ([],[])
   freshTVars tn ((variance,tv,mk) : vs) = do
    let pk = case mk of CBox eo -> MkPolyKind [] eo; _ -> error "not implemented"
    (vartypes,vs') <- freshTVars tn vs
    (tyPos, tyNeg) <- freshTVar (TypeParameter tn tv) (Just (MkPknd pk))
    case (variance, rep) of
      (Covariant, PosRep)     -> pure (TST.CovariantType tyPos     : vartypes, (tyPos, tyNeg) : vs')
      (Covariant, NegRep)     -> pure (TST.CovariantType tyNeg     : vartypes, (tyPos, tyNeg) : vs')
      (Contravariant, PosRep) -> pure (TST.ContravariantType tyNeg : vartypes, (tyPos, tyNeg) : vs')
      (Contravariant, NegRep) -> pure (TST.ContravariantType tyPos : vartypes, (tyPos, tyNeg) : vs')

replaceUniVars :: (TST.PrdCnsType pol,TST.PrdCnsType pol1) -> GenM (TST.PrdCnsType pol)
replaceUniVars (TST.PrdCnsType PrdRep _,TST.PrdCnsType CnsRep _) = error "can't happen"
replaceUniVars (TST.PrdCnsType CnsRep _,TST.PrdCnsType PrdRep _) = error "can't happen"
replaceUniVars (TST.PrdCnsType PrdRep ty1,TST.PrdCnsType PrdRep ty2) = case (ty1, ty2) of 
  (TST.TyUniVar loc pol knd uv, TST.TyApp _ _ eo _ tyn args) -> do 
    let argKnds = TST.getKind <$> args
    let vars =  (\case  TST.CovariantType _ -> Covariant;  TST.ContravariantType _ -> Contravariant) <$> args
    uVars <- mapM (freshTVar TypeClassResolution) (Just <$> argKnds)
    let newArgsPos =  argToVarTy PosRep <$> NE.zip uVars vars
    let newArgsNeg =  argToVarTy NegRep <$> NE.zip uVars vars
    (newUVarPos, newUVarNeg) <- freshTVar TypeClassResolution (Just knd)
    let newTyPos = TST.TyApp loc PosRep eo newUVarPos tyn newArgsPos
    let newTyNeg = TST.TyApp loc NegRep eo newUVarNeg tyn newArgsNeg
    case pol of 
      PosRep -> do
        addConstraint $ SubType ApplicationSubConstraint ty1 newTyNeg
        addConstraint $ SubType ApplicationSubConstraint newTyPos (TST.TyUniVar loc NegRep knd uv)
        return $ TST.PrdCnsType PrdRep newTyPos
      NegRep -> do
        addConstraint $ SubType ApplicationSubConstraint newTyPos ty1
        addConstraint $ SubType ApplicationSubConstraint (TST.TyUniVar loc PosRep knd uv) newTyNeg
        return $ TST.PrdCnsType PrdRep newTyNeg
  _ -> return $ TST.PrdCnsType PrdRep ty1
replaceUniVars (TST.PrdCnsType CnsRep ty1,TST.PrdCnsType CnsRep ty2) = case (ty1,ty2) of 
  (TST.TyUniVar loc pol knd uv, TST.TyApp _ _ eo _ tyn args) -> do
    let argKnds = TST.getKind <$> args
    let vars =  (\case  TST.CovariantType _ -> Covariant;  TST.ContravariantType _ -> Contravariant) <$> args
    uVars <- mapM (freshTVar TypeClassResolution) (Just <$> argKnds)
    let newArgsPos =  argToVarTy PosRep <$> NE.zip uVars vars
    let newArgsNeg =  argToVarTy NegRep <$> NE.zip uVars vars
    (newUVarPos, newUVarNeg) <- freshTVar TypeClassResolution (Just knd)
    let newTyPos = TST.TyApp loc PosRep eo newUVarPos tyn newArgsPos
    let newTyNeg = TST.TyApp loc NegRep eo newUVarNeg tyn newArgsNeg
    case pol of 
      PosRep -> do
        addConstraint $ SubType ApplicationSubConstraint ty1 newTyNeg
        addConstraint $ SubType ApplicationSubConstraint newTyPos (TST.TyUniVar loc NegRep knd uv)
        return $ TST.PrdCnsType CnsRep newTyPos
      NegRep -> do
        addConstraint $ SubType ApplicationSubConstraint newTyPos ty1
        addConstraint $ SubType ApplicationSubConstraint (TST.TyUniVar loc PosRep knd uv) newTyNeg
        return $ TST.PrdCnsType CnsRep newTyNeg
  _ -> return $ TST.PrdCnsType CnsRep ty1

argToVarTy :: PolarityRep pol -> ((TST.Typ Pos,TST.Typ Neg),Variance) -> TST.VariantType pol
argToVarTy PosRep ((ty,_),Covariant)     = TST.CovariantType ty
argToVarTy PosRep ((_,ty),Contravariant) = TST.ContravariantType ty 
argToVarTy NegRep ((ty,_),Contravariant) = TST.ContravariantType ty
argToVarTy NegRep ((_,ty),Covariant)     = TST.CovariantType ty

createMethodSubst :: Loc -> ClassDeclaration -> GenM (TST.Bisubstitution TST.SkolemVT, [UniTVar])
createMethodSubst loc decl =
  let pkArgs = decl.classdecl_kinds.kindArgs
      cn = decl.classdecl_name
  in do
    (vars, uvs) <- freshTVars cn pkArgs
    pure (paramsMap pkArgs vars, uvs)
   where
   freshTVars ::  ClassName -> [(Variance,SkolemTVar, MonoKind)] -> GenM ([(TST.Typ Pos, TST.Typ Neg)], [UniTVar])
   freshTVars _ [] = pure ([], [])
   freshTVars cn ((variance,tv,mk) : vs) = do
    let pk = case mk of CBox eo -> MkPolyKind [] eo; _ -> error "not implemented"
    (vs', uvs) <- freshTVars cn vs
    (tyPos, tyNeg) <- freshTVar (TypeClassInstance cn tv) (Just (MkPknd pk))
    case tyPos of
      (TST.TyUniVar _ _ _ uv) -> do
        addConstraint $ case variance of
          Covariant -> TypeClass (InstanceConstraint loc) cn uv
          Contravariant -> TypeClass (InstanceConstraint loc) cn uv
        pure ((tyPos, tyNeg) : vs', uv : uvs)
      _ -> error "freshTVar should have generated a TyUniVar"


paramsMap :: [(Variance, SkolemTVar, MonoKind)]-> [(TST.Typ Pos, TST.Typ Neg)] -> TST.Bisubstitution TST.SkolemVT
paramsMap kindArgs freshVars =
  TST.MkBisubstitution (M.fromList (zip ((\(_,tv,_) -> tv) <$> kindArgs) freshVars))

insertSkolemsClass :: RST.ClassDeclaration -> GenM()
insertSkolemsClass decl = do
  let tyParams = decl.classdecl_kinds.kindArgs
  skMap <- gets (\x -> x.usedSkolemVars)
  let newM = insertSkolems tyParams skMap
  modify (\gs@GenerateState{} -> gs {usedSkolemVars = newM})
  return ()
  where
    insertSkolems :: [(Variance,SkolemTVar,MonoKind)] -> M.Map SkolemTVar PolyKind -> M.Map SkolemTVar PolyKind
    insertSkolems [] mp = mp
    insertSkolems ((_,tv,CBox eo):rst) mp = insertSkolems rst (M.insert tv (MkPolyKind [] eo) mp)
    insertSkolems ((_,tv,primk):_) _ = error ("Skolem Variable " <> show tv <> " can't have kind " <> show primk)

---------------------------------------------------------------------------------------------
-- Running computations in an extended context or environment
---------------------------------------------------------------------------------------------

withContext :: TST.LinearContext 'Pos -> GenM a -> GenM a
withContext ctx = local (\(env,gr) -> (env, gr { context = ctx : gr.context }))

---------------------------------------------------------------------------------------------
-- Looking up types in the context and environment
---------------------------------------------------------------------------------------------

-- | Lookup a type of a bound variable in the context.
lookupContext :: Loc -> PrdCnsRep pc -> Index -> GenM (TST.Typ (PrdCnsToPol pc))
lookupContext loc rep idx@(i,j) = do
  let rep' = case rep of PrdRep -> Prd; CnsRep -> Cns
  ctx <- asks ((\x -> x.context) . snd)
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
instantiateTypeScheme fv loc ts = do 
  freshVars <- forM ts.ts_vars (\(tv,knd) -> freshTVar (TypeSchemeInstance fv loc) (Just $ MkPknd knd) >>= \ty -> return (tv, ty))
-- I think this is not needed, as the constarints are already generated before this is called
--  mapM_ (addKindConstr loc (TST.getKind ts.ts_monotype)) (map snd freshVars)
  pure $ TST.zonk TST.SkolemRep (TST.MkBisubstitution (M.fromList freshVars)) ts.ts_monotype
--  where 
--    addKindConstr :: Loc -> AnyKind -> (TST.Typ Pos, TST.Typ Neg) -> GenM () 
--      case (TST.getKind ty, TST.getKind typos, TST.getKind tyneg) of 
--        (MkPknd pk1, MkPknd pk2, MkPknd pk3) -> do
--          addConstraint $ KindEq KindConstraint (MkPknd pk1) (MkPknd pk2)
--          addConstraint $ KindEq KindConstraint (MkPknd pk1) (MkPknd pk3)
--          return () 
--        (primk1, primk2, primk3) -> 
--          if primk1 == primk2 && primk1 == primk3 then return () 
--         else throwOtherError loc ["Kinds " <> ppPrint (TST.getKind ty) <> " and " <> ppPrint (TST.getKind typos) <> " don't match"]
        

---------------------------------------------------------------------------------------------
-- Adding a constraint
---------------------------------------------------------------------------------------------

-- | Add a constraint to the state.
addConstraint :: Constraint ConstraintInfo -> GenM ()
addConstraint c = modify foo
  where
    foo gs = gs { constraintSet = bar gs.constraintSet }
    bar cs = cs { cs_constraints = c:cs.cs_constraints }


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
  let declared = (\x -> x.sig_name) <$> fst decl.data_xtors
  forM_ matched $ \xn -> unless (xn `elem` declared)
    (throwGenError (PatternMatchAdditional loc xn decl.data_name))

-- | Checks for a given list of XtorNames and a type declaration whether all xtors of the type declaration
-- are matched against (Exhaustiveness).
checkExhaustiveness :: Loc
                    -> [XtorName] -- ^ The xtor names used in the pattern match
                    -> TST.DataDecl   -- ^ The type declaration to check against.
                    -> GenM ()
checkExhaustiveness loc matched decl = do
  let declared = (\x -> x.sig_name) <$> fst decl.data_xtors
  forM_ declared $ \xn -> unless (xn `elem` matched)
    (throwGenError (PatternMatchMissingXtor loc xn decl.data_name))

-- | Check well-definedness of an instance, i.e. every method specified in the class declaration is implemented
-- in the instance declaration and every implemented method is actually declared.
checkInstanceCoverage :: Loc
                      -> RST.ClassDeclaration -- ^ The class declaration to check against.
                      -> [MethodName]         -- ^ The methods implemented in the instance.
                      -> GenM ()
checkInstanceCoverage loc decl instanceMethods = do
  let classMethods = (\x -> x.msig_name) <$> fst decl.classdecl_methods
  forM_ classMethods $ \m -> unless (m `elem` instanceMethods)
    (throwGenError (InstanceImplementationMissing loc m))
  forM_ instanceMethods $ \m -> unless (m `elem` classMethods)
    (throwGenError (InstanceImplementationAdditional loc m))
