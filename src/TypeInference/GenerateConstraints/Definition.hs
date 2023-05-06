module TypeInference.GenerateConstraints.Definition
  ( -- Constraint Generation Monad
    GenM
  , GenerateReader(..)
  , GenConstraints(..)
  , runGenM
  -- generate fresh skolem variables for polykinded refinement types
  , freshSkolems
  -- Generating fresh unification variables
  , freshTVar
  , freshTVars
  , freshTVarsForTypeParams
  -- also greates unification variables for type arguments, but specific to refinement types
  , getTypeArgsRef
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
import Data.Map ( Map )
import Data.Map qualified as M
import Data.Text qualified as T
import Data.List.NonEmpty (NonEmpty(..))
import TypeInference.Environment
import Errors
import Errors.Renamer
import Syntax.RST.Types qualified as RST
import Syntax.TST.Types qualified as TST
import Syntax.CST.Names
import Syntax.CST.Types (PrdCnsRep(..), PrdCns(..), PolyKind(..), Variance(..), MonoKind(..))
import Syntax.RST.Types (Polarity(..), PolarityRep(..))
import Syntax.RST.Program as RST
import Syntax.RST.Names
import Syntax.RST.Kinds
import Syntax.TST.Program as TST
import Syntax.LocallyNameless (Index)
import TypeInference.Constraints
import Loc ( Loc, defaultLoc )
import Utils ( indexMaybe, enumerate, distribute3 )

---------------------------------------------------------------------------------------------
-- GenerateState:
--
-- We use varCount for generating fresh type variables.
-- We collect all generated unification variables and constraints in a ConstraintSet.
---------------------------------------------------------------------------------------------
data GenerateState = GenerateState
  { uVarCount :: Int
  , kVarCount :: Int
  , skVarCount :: Int
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
                               , skVarCount = 0
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

-- these are used to make sure refinement types have unique bound variables
-- otherwise they will just use the ones defined in the declaration and there will be shadowing
freshSkolems :: PolyKind -> GenM ([SkolemTVar], TST.Bisubstitution TST.SkolemVT)
freshSkolems pk = do 
  skVarC <- gets (\x -> x.skVarCount)
  skolems <- forM (enumerate pk.kindArgs) (\(i,(_,sk,mk)) -> do
    let newSk = MkSkolemTVar ("a" <> T.pack (show (skVarC+i)))
    let skPos = TST.TySkolemVar defaultLoc PosRep (monoToAnyKind mk) newSk
    let skNeg = TST.TySkolemVar defaultLoc NegRep (monoToAnyKind mk) newSk
    let bisubstPair = (sk,(skPos,skNeg))
    return (newSk,bisubstPair))  
  modify (\gs -> gs {skVarCount = skVarC + length pk.kindArgs}) 
  let bisubst = TST.MkBisubstitution $ M.fromList (snd <$> skolems)
  return (fst <$> skolems,bisubst)

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

-- like freshTVarsForTypeParams, but for refinement types
-- also creates a bisubstitution replacing the bound skolem vars of a refinement type with the unification variables
getTypeArgsRef :: Loc -> TST.DataDecl -> [SkolemTVar] -> GenM ([TST.VariantType Pos], [TST.VariantType Neg],TST.Bisubstitution TST.SkolemVT)
getTypeArgsRef loc decl skolems =  do 
  let kndArgs = decl.data_kind.kindArgs
  if length skolems == length kndArgs then do
    vars <- forM (zip kndArgs skolems) (\ ((var, _, mk),sk) -> do 
      (uvarPos, uvarNeg) <- freshTVar (TypeParameter decl.data_name sk) (Just (monoToAnyKind mk))
      let mapPair = (sk,(uvarPos,uvarNeg))
      case var of
        Covariant -> return (TST.CovariantType uvarPos, TST.CovariantType uvarNeg, mapPair)
        Contravariant -> return (TST.ContravariantType uvarNeg, TST.ContravariantType uvarPos,mapPair))
    let (varsPos,varsNeg,mapPairs) = distribute3 vars
    let bisubstMap = M.fromList mapPairs
    return (varsPos,varsNeg,TST.MkBisubstitution bisubstMap)
  else 
    throwOtherError loc ["Not enough skolem variables bound in refinement type"] 

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
