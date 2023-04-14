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
  , getTypeArgsRef
  , getSubstTypesRef
  , freshTVarsXCaseRef 
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
import Debug.Trace
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Writer
import Data.Map ( Map )
import Data.Map qualified as M
import Data.Text qualified as T
import Data.List.NonEmpty (NonEmpty((:|)))

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
  , usedSkolemVars :: M.Map SkolemTVar AnyKind
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
    let pk = monoToAnyKind mk 
    (vartypes,vs') <- freshTVars tn vs
    (tyPos, tyNeg) <- freshTVar (TypeParameter tn tv) (Just pk)
    case (variance, rep) of
      (Covariant, PosRep)     -> pure (TST.CovariantType tyPos     : vartypes, (tyPos, tyNeg) : vs')
      (Covariant, NegRep)     -> pure (TST.CovariantType tyNeg     : vartypes, (tyPos, tyNeg) : vs')
      (Contravariant, PosRep) -> pure (TST.ContravariantType tyNeg : vartypes, (tyPos, tyNeg) : vs')
      (Contravariant, NegRep) -> pure (TST.ContravariantType tyPos : vartypes, (tyPos, tyNeg) : vs')

-- these functins are specific to refinement types as they require handling type arguments differently
getTypeArgsRef :: TST.DataDecl -> GenM ([TST.VariantType Pos], [TST.VariantType Neg])
getTypeArgsRef decl =  do 
  let kndArgs = decl.data_kind.kindArgs
  vars <- forM kndArgs (\ (var, sk, mk) -> do 
    (uvarPos, uvarNeg) <- freshTVar (TypeParameter decl.data_name sk) (Just (monoToAnyKind mk))
    case var of
      Covariant -> return (TST.CovariantType uvarPos, TST.CovariantType uvarNeg, uvarPos,uvarNeg)
      Contravariant -> return (TST.ContravariantType uvarNeg, TST.ContravariantType uvarPos,uvarPos,uvarNeg))
  let varsPos = (\(x,_,_,_) -> x) <$> vars
  let varsNeg = (\(_,x,_,_) -> x) <$> vars
  return (varsPos,varsNeg)

replaceUniVarRef :: TST.PrdCnsType pol -> TST.PrdCnsType pol1 -> (NonEmpty (TST.VariantType Pos), NonEmpty (TST.VariantType Neg)) -> ConstraintInfo -> GenM (TST.PrdCnsType pol)
replaceUniVarRef (TST.PrdCnsType PrdRep _) (TST.PrdCnsType CnsRep _) _ _ = error "Can't happen"
replaceUniVarRef (TST.PrdCnsType CnsRep _) (TST.PrdCnsType PrdRep _) _ _ = error "Can't happen"
replaceUniVarRef pc1@(TST.PrdCnsType PrdRep ty1) (TST.PrdCnsType PrdRep ty2) tyArgs info = case (ty1,ty2) of 
  (TST.TyUniVar loc pol knd _,TST.TyApp _ _ eo ty tyn _) -> do
    (uvarPos,uvarNeg) <- freshTVar (RefinementArgument loc) (Just $ TST.getKind ty)
    trace ("generated " <> show uvarPos) $ pure ()
    addConstraint $ KindEq ReturnKindConstraint knd (MkPknd (MkPolyKind [] eo))
    let newTyPos = TST.TyApp loc PosRep eo uvarPos tyn (fst tyArgs)
    let newTyNeg = TST.TyApp loc NegRep eo uvarNeg tyn (snd tyArgs)
    case pol of 
      PosRep -> do 
        addConstraint $ SubType info ty1 newTyNeg
        return (TST.PrdCnsType PrdRep newTyPos)
      NegRep -> do
        addConstraint $ SubType info newTyPos ty1
        return (TST.PrdCnsType PrdRep newTyNeg)
  _ -> return pc1
replaceUniVarRef pc1@(TST.PrdCnsType CnsRep ty1) (TST.PrdCnsType CnsRep ty2) tyArgs info = case (ty1,ty2) of 
  (TST.TyUniVar loc pol knd _,TST.TyApp _ _ eo ty tyn _) -> do
    (uvarPos,uvarNeg) <- freshTVar (RefinementArgument loc) (Just $ TST.getKind ty)
    addConstraint $ KindEq ReturnKindConstraint knd (MkPknd (MkPolyKind [] eo))
    let newTyPos = TST.TyApp loc PosRep eo uvarPos tyn (fst tyArgs)
    let newTyNeg = TST.TyApp loc NegRep eo uvarNeg tyn (snd tyArgs)
    case pol of 
      PosRep -> do 
        addConstraint $ SubType info ty1 newTyNeg
        return (TST.PrdCnsType CnsRep newTyPos)
      NegRep -> do
        addConstraint $ SubType info newTyPos ty1
        return (TST.PrdCnsType CnsRep newTyNeg)
  _ -> return pc1

freshTVarsXCaseRef :: Loc -> XtorName -> ([TST.VariantType Pos], [TST.VariantType Neg]) -> [(PrdCns, Maybe FreeVarName)] -> GenM (TST.LinearContext Pos, TST.LinearContext Neg)
freshTVarsXCaseRef loc xt ([],[]) args = do 
  xtor <- lookupXtorSig loc xt PosRep
  let argKnds = map TST.getKind xtor.sig_args
  let tVarArgs = zipWith (curry (\ ((x, y), z) -> (x, y, z))) args argKnds
  freshTVars tVarArgs
freshTVarsXCaseRef _ _ ([],_) _ = error "impossible"
freshTVarsXCaseRef _ _ (_,[]) _ = error "impossible"
freshTVarsXCaseRef loc xt (fstPos:rstPos, fstNeg:rstNeg) args = do 
  xtor <- lookupXtorSig loc xt PosRep
--  let xtor' = TST.zonk TST.SkolemRep tyParamsMap xtor
  let tyArgs = (fstPos :| rstPos, fstNeg :| rstNeg)
  prdCnsTys <- forM (zip args xtor.sig_args) (freshTVarRef loc tyArgs)
  return (fst <$> prdCnsTys,snd <$> prdCnsTys)
  where 
    freshTVarRef :: Loc -> (NonEmpty (TST.VariantType Pos), NonEmpty (TST.VariantType Neg)) -> ((PrdCns,Maybe FreeVarName),TST.PrdCnsType pol) -> GenM (TST.PrdCnsType Pos,TST.PrdCnsType Neg)
    freshTVarRef loc _ ((Prd,_),TST.PrdCnsType CnsRep _) = throwOtherError loc ["Xtor argument has to be consumer, was producer"]
    freshTVarRef loc _ ((Cns,_),TST.PrdCnsType PrdRep _) = throwOtherError loc ["Xtor argument has to be consumer, was producer"]
    freshTVarRef _ argTys ((Prd,fv),TST.PrdCnsType PrdRep ty) = case ty of 
      TST.TyApp loc' _ eo ty tyn _ -> do
        (tyPos, tyNeg) <- freshTVar (ProgramVariable (fromMaybeVar fv)) (Just (TST.getKind ty))
        trace ("generated in freshTVarRef " <>show tyPos) $ pure ()
        let newTyPos = TST.TyApp loc' PosRep eo tyPos tyn (fst argTys)
        let newTyNeg = TST.TyApp loc' NegRep eo tyNeg tyn (snd argTys)
        return (TST.PrdCnsType PrdRep newTyPos, TST.PrdCnsType PrdRep newTyNeg) 
      uvPos@(TST.TyUniVar loc PosRep knd uv) -> do 
        let uvNeg = TST.TyUniVar loc NegRep knd uv
        return (TST.PrdCnsType PrdRep uvPos, TST.PrdCnsType PrdRep uvNeg)
      uvNeg@(TST.TyUniVar loc NegRep knd uv) -> do 
        let uvPos = TST.TyUniVar loc PosRep knd uv 
        return (TST.PrdCnsType PrdRep uvPos, TST.PrdCnsType PrdRep uvNeg)
      skPos@(TST.TySkolemVar loc PosRep pk sk) -> do 
        let skNeg = TST.TySkolemVar loc NegRep pk sk
        return (TST.PrdCnsType PrdRep skPos, TST.PrdCnsType PrdRep skNeg)
      skNeg@(TST.TySkolemVar loc NegRep pk sk) -> do 
        let skPos = TST.TySkolemVar loc PosRep pk sk
        return (TST.PrdCnsType PrdRep skPos, TST.PrdCnsType PrdRep skNeg)
      _ -> do
        let knd = TST.getKind ty
        (tp, tn) <- freshTVar (ProgramVariable (fromMaybeVar fv)) (Just knd)
        return (TST.PrdCnsType PrdRep tp,TST.PrdCnsType PrdRep tn)
    freshTVarRef _ argTys ((Cns,fv),TST.PrdCnsType CnsRep ty) = case ty of 
      TST.TyApp loc' _ eo ty tyn _ -> do 
        (tyPos, tyNeg) <- freshTVar (ProgramVariable (fromMaybeVar fv)) (Just (TST.getKind ty))
        let newTyPos = TST.TyApp loc' PosRep eo tyPos tyn (fst argTys)
        let newTyNeg = TST.TyApp loc' NegRep eo tyNeg tyn (snd argTys)
        return (TST.PrdCnsType CnsRep newTyNeg, TST.PrdCnsType CnsRep newTyPos)
      uvPos@(TST.TyUniVar loc PosRep knd uv) -> do 
        let uvNeg = TST.TyUniVar loc NegRep knd uv
        return (TST.PrdCnsType CnsRep uvNeg, TST.PrdCnsType CnsRep uvPos)
      uvNeg@(TST.TyUniVar loc NegRep knd uv) -> do 
        let uvPos = TST.TyUniVar loc PosRep knd uv 
        return (TST.PrdCnsType CnsRep uvNeg, TST.PrdCnsType CnsRep uvPos)
      skPos@(TST.TySkolemVar loc PosRep pk sk) -> do 
        let skNeg = TST.TySkolemVar loc NegRep pk sk
        return (TST.PrdCnsType CnsRep skNeg, TST.PrdCnsType CnsRep skPos)
      skNeg@(TST.TySkolemVar loc NegRep pk sk) -> do 
        let skPos = TST.TySkolemVar loc PosRep pk sk
        return (TST.PrdCnsType CnsRep skNeg, TST.PrdCnsType CnsRep skPos)
      _ -> do 
        let knd = TST.getKind ty 
        (tp,tn) <- freshTVar (ProgramVariable (fromMaybeVar fv)) (Just knd)
        return (TST.PrdCnsType CnsRep tn, TST.PrdCnsType CnsRep tp)
 

getSubstTypesRef :: [TST.PrdCnsType pol] -> [TST.PrdCnsType pol1] -> ([TST.VariantType Pos], [TST.VariantType Neg]) -> ConstraintInfo -> GenM [TST.PrdCnsType pol]
getSubstTypesRef substTypes _ ([],[]) _ = return substTypes 
getSubstTypesRef substTypes sig_args (fstPos:rstPos,fstNeg:rstNeg) info = forM (zip substTypes sig_args) (\(x,y) -> replaceUniVarRef x y (fstPos :| rstPos, fstNeg :| rstNeg) info)
getSubstTypesRef _ _ _ _ = error "impossible (there are always the same amount of positive and negative univars"

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
    insertSkolems :: [(Variance,SkolemTVar,MonoKind)] -> M.Map SkolemTVar AnyKind -> M.Map SkolemTVar AnyKind
    insertSkolems [] mp = mp
    insertSkolems ((_,tv,CBox eo):rst) mp = insertSkolems rst (M.insert tv (MkPknd $ MkPolyKind [] eo) mp)
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
