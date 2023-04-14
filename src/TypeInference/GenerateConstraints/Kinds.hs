module TypeInference.GenerateConstraints.Kinds
  ( AnnotateKind(..)
  , getKindDecl
  , resolveDataDecl
  ) where


import Syntax.TST.Program qualified as TST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.RST.Names
import Syntax.RST.Kinds
import Syntax.TST.Types qualified as TST
import Syntax.TST.Types (getKind)
import Syntax.CST.Kinds
import Syntax.CST.Names 
import Pretty.Pretty
import Pretty.Types()
import Errors
import Loc
import TypeInference.Constraints
import TypeInference.GenerateConstraints.Definition
import TypeInference.Environment

import Control.Monad.Reader
import Control.Monad.Except
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NE
import Control.Monad.State
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Bifunctor (bimap)
import qualified Syntax.CST.Types as CST
import Syntax.RST.Types (Polarity(..), PolarityRep (..))

--------------------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------------------

getXtorKinds :: Loc -> [RST.XtorSig pol] -> GenM EvaluationOrder
getXtorKinds loc [] = throwSolverError loc ["Can't find kinds of empty List of Xtors"]
getXtorKinds loc [xtor] = do
  let nm = xtor.sig_name
  lookupXtorKind loc nm 
getXtorKinds loc (xtor:xtors) = do 
  let nm = xtor.sig_name
  eo <- lookupXtorKind loc nm
  eo' <- getXtorKinds loc xtors
  -- all constructors of a structural type need to have the same return kind
  addConstraint (KindEq ReturnKindConstraint (MkPknd (MkPolyKind [] eo)) (MkPknd (MkPolyKind [] eo')))
  return eo
  
getKindDecl ::  TST.DataDecl -> GenM (MonoKind,[MonoKind])
getKindDecl decl = do
  -- this can never be a kind var
  let polyknd = decl.data_kind
  let argKnds = map (\(_,_,mk) -> mk) polyknd.kindArgs
  return (CBox polyknd.returnKind, argKnds)

checkXtorKind :: Loc -> Maybe RnTypeName -> TST.XtorSig pol -> GenM () 
-- refinement type
checkXtorKind loc (Just tyn) xtor = do 
  decl <- lookupTypeName loc tyn
  let declXtor = filter (\x -> x.sig_name == xtor.sig_name) (fst decl.data_xtors)
  case declXtor of 
    [] -> throwOtherError loc ["Xtor " <> ppPrint xtor.sig_name <> " not found in environment"]
    [declXtor] -> do 
      if length declXtor.sig_args /= length xtor.sig_args then throwOtherError loc ["Number of xtor arguments does not match declaration"]
      else do 
        let kindPairs = zip (map TST.getKind declXtor.sig_args) (map TST.getKind xtor.sig_args)
        let constrs = map (uncurry (KindEq KindConstraint)) kindPairs
        mapM_ addConstraint constrs
    _ -> throwOtherError loc ["found multiple declarations for xtor " <> ppPrint xtor.sig_name]
-- structural type
checkXtorKind loc Nothing xtor = do 
  structXtor <- lookupStructuralXtor xtor.sig_name
  if length structXtor.strxtordecl_arity /= length xtor.sig_args then throwOtherError loc ["Number of xtor arguments does not match declaration"] 
  else do   
    let kindPairs = zip (map (monoToAnyKind . snd) structXtor.strxtordecl_arity) (map TST.getKind xtor.sig_args)
    let constrs = map (uncurry (KindEq KindConstraint)) kindPairs 
    mapM_ addConstraint constrs

checkVariance :: (Variance,TST.VariantType pol) -> Bool
checkVariance (Covariant, TST.CovariantType _) = True
checkVariance (Contravariant, TST.ContravariantType _) = True 
checkVariance _ = False 

checkVariantTypes :: Loc -> PolyKind -> NonEmpty (TST.VariantType pol) -> GenM EvaluationOrder
checkVariantTypes loc (MkPolyKind kndArgs eo) args = 
  if length kndArgs /= length args then 
    throwOtherError loc ["Number of Type Arguments does not match declaration"]
  else do
    let argsLs = NE.toList args
    -- check variances
    let kndVars = map (\(x,_,_) -> x) kndArgs 
    let varsChecked = zipWith (curry checkVariance) kndVars argsLs
    if all (==True) varsChecked then do
      let declKnds = map (\(_,_,z) -> z) kndArgs
      let argKnds = map TST.getKind argsLs 
      let kindEqs = zip declKnds argKnds
      mapM_ (\(x,y) -> addConstraint (KindEq TypeArgKindConstraint y (monoToAnyKind x))) kindEqs
      return eo
    else throwOtherError loc ["Variances of applied types don't match"]
checkVariantTypes loc (KindVar _) _ = throwOtherError loc ["Polykind of application unclear"]

newKVar :: GenM KVar
newKVar = do
  kvCnt <- gets (\x -> x.kVarCount)
  let kVar = MkKVar (T.pack ("kv" <> show kvCnt))
  modify (\gs@GenerateState{} -> gs { kVarCount = kvCnt + 1 })
  modify (\gs -> gs { constraintSet = gs.constraintSet {cs_kvars = gs.constraintSet.cs_kvars ++ [kVar] } })
  return kVar 

--------------------------------------------------------------------------------------------
-- Annotating Data Declarations 
--------------------------------------------------------------------------------------------

data DataDeclState = MkDataDeclState
  {
    declKind :: PolyKind,
    declTyName :: RnTypeName,
    boundRecVars :: M.Map RecTVar MonoKind,
    refXtors :: ([TST.XtorSig RST.Pos], [TST.XtorSig RST.Neg]),
    refRecVars :: M.Map RecTVar PolyKind
  }

createDataDeclState :: PolyKind -> RnTypeName -> DataDeclState
createDataDeclState polyknd tyn = MkDataDeclState 
  { declKind = polyknd,
    declTyName = tyn,
    boundRecVars = M.empty, 
    refXtors = ([],[]), 
    refRecVars = M.empty
  }

type DataDeclM a = (ReaderT (M.Map ModuleName Environment, ()) (StateT DataDeclState (Except (NonEmpty Error)))) a

runDataDeclM :: DataDeclM a -> M.Map ModuleName Environment -> DataDeclState -> Either (NonEmpty Error) (a,DataDeclState)
runDataDeclM m env initSt = runExcept (runStateT (runReaderT m (env,())) initSt)

resolveDataDecl :: RST.DataDecl -> M.Map ModuleName Environment ->  Either (NonEmpty Error) TST.DataDecl
resolveDataDecl decl env = do
  (decl', _) <- runDataDeclM (annotateDataDecl decl) env (createDataDeclState decl.data_kind decl.data_name)
  return decl' 

addRecVar :: RecTVar -> PolyKind -> DataDeclM () 
addRecVar rv pk = modify (\s@MkDataDeclState{refRecVars = recVarMap} -> s {refRecVars = M.insert rv pk recVarMap})

addXtors :: ([TST.XtorSig RST.Pos],[TST.XtorSig RST.Neg]) -> DataDeclM ()
addXtors newXtors =  modify (\s@MkDataDeclState{refXtors = xtors} -> 
                                s {refXtors = Data.Bifunctor.bimap (fst xtors ++ ) (snd xtors ++) newXtors })

getXtors :: RST.PolarityRep pol -> [XtorName] -> DataDeclM [TST.XtorSig pol]
getXtors pl names = do
  cached <- gets (\x -> x.refXtors)
  let f = filter (\(x::TST.XtorSig RST.Pos) -> x.sig_name `elem` names)
  let g = filter (\(x::TST.XtorSig RST.Neg) -> x.sig_name `elem` names)
  case pl of 
    RST.PosRep -> return (f (fst cached))
    RST.NegRep -> return (g (snd cached))
  
annotXtor :: RST.XtorSig pol -> DataDeclM (TST.XtorSig pol)
annotXtor (RST.MkXtorSig nm ctxt) = do 
  ctxt' <- annotCtxt ctxt
  return $ TST.MkXtorSig nm ctxt'

annotCtxt :: RST.LinearContext pol -> DataDeclM (TST.LinearContext pol)
annotCtxt [] = return []
annotCtxt (RST.PrdCnsType pc ty:rst) = do 
  rst' <- annotCtxt rst
  ty' <- annotTy ty
  return $ TST.PrdCnsType pc ty' : rst'

annotVarTy :: RST.VariantType pol -> DataDeclM (TST.VariantType pol)
annotVarTy (RST.CovariantType ty) = do
  ty' <- annotTy ty
  return $ TST.CovariantType ty' 
annotVarTy (RST.ContravariantType ty) = do 
  ty' <- annotTy ty 
  return $ TST.ContravariantType ty'


getKindSkolem :: PolyKind -> SkolemTVar -> PolyKind
getKindSkolem polyknd = searchKindArgs polyknd.kindArgs
  where 
    searchKindArgs :: [(Variance, SkolemTVar, MonoKind)] -> SkolemTVar -> PolyKind
    searchKindArgs [] _ = error "Skolem Variable not found in argument types of polykind"
    searchKindArgs ((_,tv,CBox eo):rst) tv' = if tv == tv' then MkPolyKind [] eo else searchKindArgs rst tv'
    searchKindArgs ((_,tv,knd):_) _ = error ("Skolem Variable " <> show tv <> " can't have kind " <> show knd)

annotTy :: RST.Typ pol -> DataDeclM (TST.Typ pol)
annotTy (RST.TySkolemVar loc pol tv) = do 
  polyknd <- gets (\x -> x.declKind)
  return $ TST.TySkolemVar loc pol (getKindSkolem polyknd tv) tv 
-- uni vars should not appear in data declarations
annotTy (RST.TyUniVar loc _ _) = throwOtherError loc ["UniVar should not appear in data declaration"]
annotTy (RST.TyRecVar loc pol tv) = do
  rVarMap <- gets (\x -> x.refRecVars)
  case M.lookup tv rVarMap of 
    Nothing -> throwOtherError loc ["Unbound RecVar " <> ppPrint tv <> " in data declaration"]
    Just pk -> return $ TST.TyRecVar loc pol pk tv
annotTy (RST.TyData loc pol xtors) = do 
  let xtnms = map (\x -> x.sig_name) xtors
  xtorKinds <- mapM (lookupXtorKind loc) xtnms
  let allEq = compXtorKinds xtorKinds
  case allEq of 
    Nothing -> throwOtherError loc ["Not all xtors have the same return kind"]
    Just eo -> do 
      xtors' <- mapM annotXtor xtors
      return $ TST.TyData loc pol eo xtors' 
  where
    compXtorKinds :: [EvaluationOrder] -> Maybe EvaluationOrder
    compXtorKinds [] = Nothing 
    compXtorKinds [eo] = Just eo
    compXtorKinds (xtor1:xtor2:rst) = if xtor1==xtor2 then compXtorKinds (xtor2:rst) else Nothing
annotTy (RST.TyCodata loc pol xtors) = do 
  let xtnms = map (\x -> x.sig_name) xtors
  xtorKinds <- mapM (lookupXtorKind loc) xtnms
  let allEq = compXtorKinds xtorKinds
  case allEq of 
    Nothing -> throwOtherError loc ["Not all xtors have the same return kind"]
    Just eo -> do 
      xtors' <- mapM annotXtor xtors
      return $ TST.TyCodata loc pol eo xtors' 
  where 
    compXtorKinds :: [EvaluationOrder] -> Maybe EvaluationOrder
    compXtorKinds [] = Nothing 
    compXtorKinds [mk] = Just mk
    compXtorKinds (xtor1:xtor2:rst) = if xtor1==xtor2 then compXtorKinds (xtor2:rst) else Nothing

annotTy (RST.TyDataRefined loc pol pknd argVars tyn xtors) = do 
  tyn' <- gets (\x -> x.declTyName)
  if tyn == tyn' then do 
    let xtorNames = map (\x->x.sig_name) xtors
    xtors' <- getXtors pol xtorNames
    return $ TST.TyDataRefined loc pol pknd argVars tyn xtors'
  else do 
    decl <- lookupTypeName loc tyn
    let xtors' = (case pol of RST.PosRep -> fst; RST.NegRep -> snd) decl.data_xtors
    return $ TST.TyDataRefined loc pol pknd argVars tyn xtors'

annotTy (RST.TyCodataRefined loc pol pknd argVars tyn xtors) = do 
  tyn' <- gets (\x -> x.declTyName)
  if tyn == tyn' then do 
    let xtorNames = map (\x->x.sig_name) xtors
    xtors' <- getXtors (RST.flipPolarityRep pol) xtorNames
    return $ TST.TyCodataRefined loc pol pknd argVars tyn xtors'
  else do 
    decl <- lookupTypeName loc tyn
    let xtors' = (case pol of RST.PosRep -> snd; RST.NegRep -> fst) decl.data_xtors
    return $ TST.TyCodataRefined loc pol pknd argVars tyn xtors'

annotTy (RST.TyApp loc pol ty tyn args) = do 
  ty' <- annotTy ty 
  args' <- mapM annotVarTy args
  let pk = TST.getKind ty'
  case pk of 
    (MkPknd (MkPolyKind kndArgs eo)) -> 
      if length args' /= length kndArgs then
        throwOtherError loc ["Number of arguments doesn't match declaration"]
      else do 
        let declVars = map (\(x,_,_) -> x) kndArgs
        let declMks = map (\(_,_,z) -> z) kndArgs
        let argMks = map TST.getKind (NE.toList args')
        let mksChecked = zipWith (curry checkMk) declMks argMks
        let varsChecked  = zipWith (curry checkVariance) declVars (NE.toList args')
        if all (==True) mksChecked && all (==True) varsChecked then
          return $ TST.TyApp loc pol eo ty' tyn args'
        else 
          throwOtherError loc ["Applied Argument Kinds " <> ppPrint args' <> " don't match kinds of declaration " <> ppPrint (MkPolyKind kndArgs eo)]
    (MkPknd (KindVar _)) -> throwOtherError loc ["Can't have a kind variable in declaration"]
    _ -> throwOtherError loc ["can't apply arguments to monokinded type"]
  where 
    checkMk :: (MonoKind,AnyKind) -> Bool
    checkMk (CBox eo1,MkPknd (MkPolyKind [] eo2)) = eo1 == eo2
    checkMk (I64Rep,MkI64) = True
    checkMk (F64Rep,MkF64) = True
    checkMk (CharRep,MkChar)  = True
    checkMk (StringRep,MkString) = True
    checkMk _ = False


annotTy (RST.TyNominal loc pol polyknd tyn) = return $ TST.TyNominal loc pol polyknd tyn
annotTy (RST.TySyn loc pol tyn ty) =  do 
  ty' <- annotTy ty
  return $ TST.TySyn loc pol tyn ty'
annotTy (RST.TyBot loc) = throwOtherError loc ["TyBot should not be contained in a data declaration"]
annotTy (RST.TyTop loc) = throwOtherError loc ["TyTop should not be contained in a data declaration"]
annotTy (RST.TyUnion loc ty1 ty2) = do 
  ty1' <- annotTy ty1 
  ty2' <- annotTy ty2
  let knd1 = getKind ty1'
  let knd2 = getKind ty2'
  if knd1 == knd2 then
    return $ TST.TyUnion loc knd1 ty1' ty2'
  else 
    throwOtherError loc ["Kinds " <> ppPrint knd1 <> " and " <> ppPrint knd2 <> " of union are not compatible"]
annotTy (RST.TyInter loc ty1 ty2) = do 
  ty1' <- annotTy ty1 
  ty2' <- annotTy ty2
  let knd1 = getKind ty1'
  let knd2 = getKind ty2'
  if knd1 == knd2 then
    return $ TST.TyInter loc knd1 ty1' ty2'
  else 
    throwOtherError loc ["Kinds " <> ppPrint knd1 <> " and " <> ppPrint knd2 <> " of union are not compatible"]
annotTy (RST.TyRec loc pol rv ty) = case ty of 
  RST.TyDataRefined loc' pol' pknd argVars tyn xtors -> do 
    addRecVar rv pknd
    xtors' <- mapM annotXtor xtors
    return $ TST.TyRec loc pol rv (TST.TyDataRefined loc' pol' pknd argVars tyn xtors')
  RST.TyCodataRefined loc' pol' pknd argVars tyn xtors -> do
    addRecVar rv pknd
    xtors' <- mapM annotXtor xtors
    return $ TST.TyRec loc pol rv (TST.TyCodataRefined loc' pol' pknd argVars tyn xtors')
  _ -> throwOtherError loc ["TyRec can only appear inside Refinement Declarations"]

annotTy (RST.TyI64 loc pol) = return $ TST.TyI64 loc pol
annotTy (RST.TyF64 loc pol) = return $ TST.TyF64 loc pol
annotTy (RST.TyChar loc pol) = return $ TST.TyChar loc pol
annotTy (RST.TyString loc pol) = return $ TST.TyString loc pol
annotTy (RST.TyFlipPol pol ty) = do 
  ty' <- annotTy ty 
  return $ TST.TyFlipPol pol ty'
annotTy (RST.TyKindAnnot mk ty) = do
  ty' <- annotTy ty
  if getKind ty' == monoToAnyKind mk then
    return ty'
  else 
    throwOtherError (getLoc ty') ["Annotated Kind " <> ppPrint mk <> " and inferred kind " <> ppPrint (getKind ty') <> " are not compatible"]

-- | Given the polarity (data/codata) and the name of a type, compute the empty refinement of that type.
-- Example:
--
--   computeEmptyRefinementType Data   Nat = < Nat | >
--   computeEmptyRefinementType Codata Foo = { Foo | }
-- 
computeEmptyRefinementType :: CST.DataCodata
                           -> RnTypeName
                           -> PolyKind
                           -> DataDeclM (RST.Typ Pos, RST.Typ Neg)
computeEmptyRefinementType CST.Data tn polyknd = do 
  pure (RST.TyDataRefined   defaultLoc PosRep polyknd [] tn [], RST.TyDataRefined   defaultLoc NegRep polyknd [] tn [])
computeEmptyRefinementType CST.Codata tn polyknd = do 
  pure (RST.TyCodataRefined defaultLoc PosRep polyknd [] tn [], RST.TyCodataRefined defaultLoc NegRep polyknd [] tn [])

-- | Given the polarity (data/codata), the name and the constructors/destructors of a type, compute the
-- full refinement of that type.
-- Example:
--
--   computeFullRefinementType Data Nat [Z,S(Nat)] = mu a. < Nat | Z, S(a) >
--
computeFullRefinementType :: CST.DataCodata
                          -> RnTypeName
                          -> ([RST.XtorSig Pos], [RST.XtorSig Neg])
                          -> PolyKind
                          -> DataDeclM (RST.Typ Pos, RST.Typ Neg)
computeFullRefinementType dc tn (xtorsPos, xtorsNeg) polyknd = do
  -- Define the variable that stands for the recursive occurrences in the translation.
  let recVar = MkRecTVar "α"
  let recVarPos = RST.TyRecVar defaultLoc PosRep recVar
  let recVarNeg = RST.TyRecVar defaultLoc NegRep recVar
  -- Replace all the recursive occurrences of the type by the variable "α" in the constructors/destructors.
  let xtorsReplacedPos :: [RST.XtorSig Pos] = RST.replaceNominal recVarPos recVarNeg tn <$> xtorsPos
  let xtorsReplacedNeg :: [RST.XtorSig Neg] = RST.replaceNominal recVarPos recVarNeg tn <$> xtorsNeg
  -- Assemble the 
  let fullRefinementTypePos :: RST.Typ Pos = case dc of
                   CST.Data   -> RST.TyRec defaultLoc PosRep recVar (RST.TyDataRefined   defaultLoc PosRep polyknd [] tn xtorsReplacedPos)
                   CST.Codata -> RST.TyRec defaultLoc PosRep recVar (RST.TyCodataRefined defaultLoc PosRep polyknd [] tn xtorsReplacedNeg)
  let fullRefinementTypeNeg :: RST.Typ Neg = case dc of
                   CST.Data   -> RST.TyRec defaultLoc NegRep recVar (RST.TyDataRefined defaultLoc NegRep polyknd [] tn    xtorsReplacedNeg)
                   CST.Codata -> RST.TyRec defaultLoc NegRep recVar (RST.TyCodataRefined defaultLoc NegRep polyknd [] tn  xtorsReplacedPos)
  pure (fullRefinementTypePos, fullRefinementTypeNeg)

annotateDataDecl :: RST.DataDecl -> DataDeclM TST.DataDecl 
annotateDataDecl RST.NominalDecl {
  data_loc = loc, 
  data_doc = doc,
  data_name = tyn,
  data_polarity = pol,
  data_kind = polyknd,
  data_xtors = xtors 
  } =do 
    xtorsPos <- mapM annotXtor (fst xtors)
    xtorsNeg <- mapM annotXtor (snd xtors)
    return TST.NominalDecl { 
        data_loc = loc, 
        data_doc = doc,
        data_name = tyn,
        data_polarity = pol,
        data_kind = polyknd,
        data_xtors = (xtorsPos, xtorsNeg) 
      }
annotateDataDecl RST.RefinementDecl { 
  data_loc = loc, 
  data_doc = doc,
  data_name = tyn,
  data_polarity = pol ,
  data_kind = polyknd,
  data_xtors = xtors
  } = do
    -- Compute the full and empty refinement types:
    (emptyPos, emptyNeg) <- computeEmptyRefinementType pol tyn polyknd
    emptPos' <- annotTy emptyPos
    emptNeg' <- annotTy emptyNeg
    (fulPos, fulNeg) <- computeFullRefinementType pol tyn xtors polyknd
    fulPos' <- annotTy fulPos
    fulNeg' <- annotTy fulNeg
    -- Compute the annotated xtors (without refinement)
    xtorsPos <- mapM annotXtor (fst xtors)
    xtorsNeg <- mapM annotXtor (snd xtors)
    addXtors (xtorsPos,xtorsNeg)
    -- Compute the refined xtors:
    let xtorsRefinedPos = RST.replaceNominal emptyPos emptyNeg tyn <$> fst xtors
    -- The negative ones are called by `getXtorSigsUpper` which are used as upper bounds to Xtors!
    let xtorsRefinedNeg = RST.replaceNominal fulPos fulNeg tyn <$> snd xtors
    xtorsRefPos <- mapM annotXtor xtorsRefinedPos
    xtorsRefNeg <- mapM annotXtor xtorsRefinedNeg
    return TST.RefinementDecl {
      data_loc = loc,
      data_doc = doc,
      data_name = tyn,
      data_polarity = pol ,
      data_refinement_empty = (emptPos', emptNeg'), 
      data_refinement_full = (fulPos', fulNeg'), 
      data_kind = polyknd,
      data_xtors = (xtorsPos, xtorsNeg),
      data_xtors_refined = (xtorsRefPos, xtorsRefNeg) 
      }

--------------------------------------------------------------------------------------------
-- checking Kinds
--------------------------------------------------------------------------------------------

class AnnotateKind a b | a -> b where
  annotateKind :: a -> GenM b

instance AnnotateKind (Maybe (RST.TypeScheme pol)) (Maybe (TST.TypeScheme pol)) where 
  annotateKind Nothing = return Nothing
  annotateKind (Just ty) = do 
   ty' <- annotateKind ty 
   return (Just ty')

instance AnnotateKind  (RST.Typ RST.Pos, RST.Typ RST.Neg) (TST.Typ RST.Pos, TST.Typ RST.Neg) where
  annotateKind ::  (RST.Typ RST.Pos, RST.Typ RST.Neg) -> GenM (TST.Typ RST.Pos, TST.Typ RST.Neg)
  annotateKind (ty1, ty2) = do 
    ty1' <- annotateKind ty1
    ty2' <- annotateKind ty2
    return (ty1', ty2')

instance AnnotateKind (RST.TypeScheme pol) (TST.TypeScheme pol) where
  annotateKind ::  RST.TypeScheme pol -> GenM (TST.TypeScheme pol)
  annotateKind RST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty} = do
    ty' <- annotateKind ty
    newTVars <- mapM addTVar tvs
    return TST.TypeScheme {ts_loc = loc, ts_vars = newTVars,ts_monotype = ty'}
    where 
      addTVar :: MaybeKindedSkolem -> GenM KindedSkolem
      addTVar (sk, mmk) = do 
        skMap <- gets (\x -> x.usedSkolemVars)
        case (M.lookup sk skMap, mmk) of 
          (Nothing, _) -> throwOtherError loc ["Skolem Variable " <> ppPrint sk <> " defined but not used"]
          (Just pk,Nothing) -> return (sk,pk)
          (Just pk, Just pk') -> do
            addConstraint $ KindEq KindConstraint (MkPknd pk) (MkPknd pk')
            return (sk,pk)
                
instance AnnotateKind (RST.VariantType pol) (TST.VariantType pol) where
  annotateKind ::  RST.VariantType pol -> GenM (TST.VariantType pol)
  annotateKind (RST.CovariantType ty) = TST.CovariantType <$> annotateKind ty
  annotateKind (RST.ContravariantType ty) = TST.ContravariantType <$> annotateKind ty

instance AnnotateKind (RST.PrdCnsType pol) (TST.PrdCnsType pol) where
  annotateKind ::  RST.PrdCnsType pol -> GenM (TST.PrdCnsType pol)
  annotateKind (RST.PrdCnsType rep ty) = do 
    ty' <- annotateKind ty
    return (TST.PrdCnsType rep ty')

instance AnnotateKind (RST.LinearContext pol) (TST.LinearContext pol) where
  annotateKind ::  RST.LinearContext pol -> GenM (TST.LinearContext pol)
  annotateKind = mapM annotateKind

instance AnnotateKind (RST.XtorSig pol) (TST.XtorSig pol) where
  annotateKind ::  RST.XtorSig pol -> GenM (TST.XtorSig pol)
  annotateKind RST.MkXtorSig { sig_name = nm, sig_args = ctxt } = do 
    ctxt' <- annotateKind ctxt 
    return (TST.MkXtorSig {sig_name = nm, sig_args = ctxt' })

instance AnnotateKind (RST.Typ pol) (TST.Typ pol) where
  annotateKind ::  RST.Typ pol -> GenM (TST.Typ pol)
  annotateKind (RST.TySkolemVar loc pol tv) = do
    skMap <- gets (\x -> x.usedSkolemVars)
    case M.lookup tv skMap of 
      Nothing -> do
        kv <- newKVar
        let newM = M.insert tv (KindVar kv) skMap
        modify (\gs@GenerateState{} -> gs { usedSkolemVars = newM })
        return (TST.TySkolemVar loc pol (KindVar kv) tv)
      Just mk -> return (TST.TySkolemVar loc pol mk tv)

  annotateKind (RST.TyUniVar loc pol tv) = do 
    uniMap <- gets (\x -> x.usedUniVars)
    case M.lookup tv uniMap of 
      Nothing -> do
        kv <- newKVar
        let newM = M.insert tv (MkPknd $ KindVar kv) uniMap
        modify (\gs@GenerateState{} -> gs { usedUniVars = newM })
        return (TST.TyUniVar loc pol (MkPknd $ KindVar kv) tv)
      Just mk -> return (TST.TyUniVar loc pol mk tv)

  annotateKind (RST.TyRecVar loc pol rv) = do
    rvMap <- gets (\x -> x.usedRecVars)
    case M.lookup rv rvMap of 
      Nothing -> do
        kv <- newKVar
        let newM = M.insert rv (KindVar kv) rvMap
        modify (\gs@GenerateState{} -> gs { usedRecVars = newM })
        return (TST.TyRecVar loc pol (KindVar kv) rv)
      Just pk -> return (TST.TyRecVar loc pol pk rv)

  annotateKind (RST.TyData loc pol xtors) = do 
    xtors' <- mapM annotateKind xtors
    eo <- getXtorKinds loc xtors
    mapM_ (checkXtorKind loc Nothing) xtors'
    return (TST.TyData loc pol eo xtors')

  annotateKind (RST.TyCodata loc pol xtors) = do  
    xtors' <- mapM annotateKind xtors
    eo <- getXtorKinds loc xtors
    mapM_ (checkXtorKind loc Nothing) xtors'
    return (TST.TyCodata loc pol eo xtors')
 
  annotateKind (RST.TyDataRefined loc pol pknd argVars tyn xtors) = do 
    xtors' <- mapM annotateKind xtors
    mapM_ (checkXtorKind loc (Just tyn)) xtors'
    return (TST.TyDataRefined loc pol pknd argVars tyn xtors')

  annotateKind (RST.TyCodataRefined loc pol pknd argVars tyn xtors) = do
    xtors' <- mapM annotateKind xtors
    mapM_ (checkXtorKind loc (Just tyn)) xtors'
    return (TST.TyCodataRefined loc pol pknd argVars tyn xtors')

  annotateKind (RST.TyApp loc pol ty tyn args) = do 
    ty' <- annotateKind ty 
    decl <- lookupTypeName loc tyn
    args' <- mapM annotateKind args
    eo <- checkVariantTypes loc decl.data_kind args'
    addConstraint $ KindEq KindConstraint (MkPknd decl.data_kind) (TST.getKind ty')
    return $ TST.TyApp loc pol eo ty' tyn args'
    
  annotateKind (RST.TyNominal loc pol polyknd tyn) = do 
    return $ TST.TyNominal loc pol polyknd tyn
              
  annotateKind (RST.TySyn loc pol tn ty) = do 
    ty' <- annotateKind ty 
    return (TST.TySyn loc pol tn ty')

  annotateKind (RST.TyBot loc) = do 
    TST.TyBot loc . MkPknd . KindVar <$> newKVar

  annotateKind (RST.TyTop loc) = do
    TST.TyTop loc . MkPknd . KindVar <$> newKVar

  annotateKind (RST.TyUnion loc ty1 ty2) = do  
    ty1' <- annotateKind ty1
    ty2' <- annotateKind ty2
    let knd1 = getKind ty1'
    let knd2 = getKind ty2'
    addConstraint $ KindEq KindConstraint knd1 knd2
    return (TST.TyUnion loc knd1 ty1' ty2')

  annotateKind (RST.TyInter loc ty1 ty2) = do
    ty1' <- annotateKind ty1
    ty2' <- annotateKind ty2
    let knd1 = getKind ty1'
    let knd2 = getKind ty2'
    addConstraint $ KindEq KindConstraint knd1 knd2
    return (TST.TyInter loc knd1 ty1' ty2')
    
  annotateKind (RST.TyRec loc pol rv ty) = do
    ty' <- annotateKind ty
    return (TST.TyRec loc pol rv ty')

  annotateKind (RST.TyI64 loc pol) = return (TST.TyI64 loc pol)
  annotateKind (RST.TyF64 loc pol) = return (TST.TyF64 loc pol)
  annotateKind (RST.TyChar loc pol) = return (TST.TyChar loc pol)
  annotateKind (RST.TyString loc pol) = return(TST.TyString loc pol)

  annotateKind (RST.TyFlipPol pol ty) = do 
    ty' <- annotateKind ty
    return (TST.TyFlipPol pol ty')
  
  annotateKind (RST.TyKindAnnot mk ty) = do 
    ty' <- annotateKind ty 
    addConstraint $ KindEq KindConstraint (getKind ty') (monoToAnyKind mk)
    return ty'
