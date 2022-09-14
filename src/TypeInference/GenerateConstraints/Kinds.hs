module TypeInference.GenerateConstraints.Kinds where

import Syntax.TST.Program qualified as TST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.TST.Types qualified as TST
import Syntax.TST.Types (getKind)
import Syntax.CST.Kinds
import Syntax.CST.Names 
import Pretty.Pretty
import Lookup
import Errors
import Loc
import TypeInference.Constraints
import TypeInference.GenerateConstraints.Definition
import Driver.Environment
import Control.Monad.Reader
import Control.Monad.Except
import Data.List.NonEmpty (NonEmpty(..))

import Control.Monad.State
import Data.Map qualified as M
import Data.Text qualified as T

--------------------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------------------
-- generates the constraints between kinds of xtor arguments and used arguments
genArgConstrs :: TST.GetKind a =>  Loc -> XtorName -> [MonoKind] -> [a] -> GenM () 
genArgConstrs _ _ [] [] = return () 
genArgConstrs loc xtornm (_:_) [] = throwOtherError loc ["Too few arguments for constructor " <> ppPrint xtornm]
genArgConstrs loc xtornm [] (_:_) = throwOtherError loc ["Too many arguments for constructor " <> ppPrint xtornm]
genArgConstrs loc xtornm (fst:rst) (fst':rst') = do 
  addConstraint (KindEq KindConstraint (getKind fst') fst)
  genArgConstrs loc xtornm rst rst'

getXtorKinds :: Loc -> [TST.XtorSig pol] -> GenM MonoKind
getXtorKinds loc [] = throwSolverError loc ["Can't find kinds of empty List of Xtors"]
getXtorKinds loc [xtor] = do
  let nm = TST.sig_name xtor
  (mk, args) <- lookupXtorKind nm 
  genArgConstrs loc nm args (TST.sig_args xtor)
  return mk
getXtorKinds loc (xtor:xtors) = do 
  let nm = TST.sig_name xtor 
  (mk, args) <- lookupXtorKind nm
  mk' <- getXtorKinds loc xtors
  genArgConstrs loc nm args (TST.sig_args xtor)
  -- all constructors of a structural type need to have the same return kind
  addConstraint (KindEq KindConstraint mk mk')
  return mk

-- returns returnkind and list of argument kinds
getTyNameKind ::  Loc -> RnTypeName -> GenM (MonoKind,[MonoKind])
getTyNameKind loc tyn = do
  decl <- lookupTypeName loc tyn
  let polyKnd = TST.data_kind decl
  let argKnds = map (\(_,_,x) -> x) (kindArgs polyKnd)
  return (CBox (returnKind polyKnd), argKnds)

getKindDecl ::  TST.DataDecl -> GenM MonoKind
getKindDecl decl = do
  let polyknd = TST.data_kind decl
  return (CBox (returnKind polyknd))
  let kVar = MkKVar (T.pack ("kv" <> show kvCnt))
  modify (\gs@GenerateState{} -> gs { kVarCount = kvCnt + 1 })
  modify (\gs@GenerateState{ constraintSet = cs@ConstraintSet { cs_kvars } } ->
            gs { constraintSet = cs {cs_kvars = cs_kvars ++ [kVar] } })
  return kVar 

--------------------------------------------------------------------------------------------
-- Annotating Data Declarations 
--------------------------------------------------------------------------------------------

data DataDeclState = DataDeclState
  {
    declKind :: PolyKind,
    declTyName :: RnTypeName,
    boundRecVars :: M.Map RecTVar MonoKind,
    usedKindVars :: [KVar],
    kvCount :: Int
  }

createDataDeclState :: PolyKind -> RnTypeName -> DataDeclState
createDataDeclState polyknd tyn = DataDeclState 
  { declKind = polyknd,
    declTyName = tyn,
    boundRecVars = M.empty, 
    usedKindVars = [], 
    kvCount = 0
  }

type DataDeclM a = (ReaderT (M.Map ModuleName Environment, ()) (StateT DataDeclState (Except (NonEmpty Error)))) a

runDataDeclM :: DataDeclM a -> M.Map ModuleName Environment -> DataDeclState -> Either (NonEmpty Error) (a,DataDeclState)
runDataDeclM m env initSt = runExcept (runStateT (runReaderT m (env,())) initSt)

resolveDataDecl :: RST.DataDecl -> M.Map ModuleName Environment ->  Either (NonEmpty Error) TST.DataDecl
resolveDataDecl decl env = do
  (decl', _) <- runDataDeclM (annotateDataDecl decl) env (createDataDeclState (RST.data_kind decl) (RST.data_name decl))
  return decl' 

addKVar :: KVar -> DataDeclM () 
addKVar kv =   modify (\(DataDeclState{declKind = knd, declTyName = tyn, boundRecVars = rvs, usedKindVars = kvs,kvCount = cnt }) 
          -> DataDeclState { declKind = knd, declTyName = tyn, boundRecVars = rvs, usedKindVars = kv : kvs, kvCount = cnt+1})

addRecVar :: RecTVar ->  MonoKind -> DataDeclM () 
addRecVar rv mk =   modify (\(DataDeclState{declKind = knd, declTyName = tyn, boundRecVars = rvs, usedKindVars = kvs,kvCount = cnt }) 
          -> DataDeclState { declKind = knd, declTyName = tyn, boundRecVars = M.insert rv mk rvs, usedKindVars = kvs, kvCount = cnt+1})

newDeclKVar :: DataDeclM KVar
newDeclKVar = do
  kvc <- gets kvCount
  let newKV = MkKVar $ T.pack ("kd"<> show kvc)
  addKVar newKV
  return newKV
  
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

annotVarTys :: [RST.VariantType pol] -> DataDeclM [TST.VariantType pol]
annotVarTys [] = return [] 
annotVarTys (RST.CovariantType ty:rst) = do
  rst' <- annotVarTys rst 
  ty' <- annotTy ty
  return $ TST.CovariantType ty' : rst'
annotVarTys (RST.ContravariantType ty:rst) = do 
  rst'<- annotVarTys rst 
  ty' <- annotTy ty 
  return $ TST.ContravariantType ty' : rst'


getKindSkolem :: PolyKind -> SkolemTVar -> MonoKind
getKindSkolem polyknd = searchKindArgs (kindArgs polyknd)
  where 
    searchKindArgs :: [(Variance, SkolemTVar, MonoKind)] -> SkolemTVar -> MonoKind
    searchKindArgs [] _ = error "Skolem Variable not found in argument types of polykind"
    searchKindArgs ((_,tv,mk):rst) tv' = if tv == tv' then mk else searchKindArgs rst tv'

annotTy :: RST.Typ pol -> DataDeclM (TST.Typ pol)
annotTy (RST.TySkolemVar loc pol tv) = do 
  polyknd <- gets declKind
  return $ TST.TySkolemVar loc pol (getKindSkolem polyknd tv) tv 
-- uni vars should not appear in data declarations
annotTy (RST.TyUniVar loc _ _) = throwOtherError loc ["UniVar should not appear in data declaration"]
annotTy (RST.TyRecVar loc pol tv) = do
  rvs <- gets boundRecVars 
  case M.lookup tv rvs of 
    Nothing -> throwOtherError loc ["Unbound RecVar " <> ppPrint tv <> " in Xtor"]
    Just knd -> return $ TST.TyRecVar loc pol knd tv
annotTy (RST.TyData loc pol xtors) = do 
  let xtnms = map RST.sig_name xtors
  xtorKinds <- mapM lookupXtorKind xtnms
  let allEq = compXtorKinds (map fst xtorKinds)
  case allEq of 
    Nothing -> throwOtherError loc ["Not all xtors have the same return kind"]
    Just mk -> do 
      xtors' <- mapM annotXtor xtors
      return $ TST.TyData loc pol mk xtors' 
  where
    compXtorKinds :: [MonoKind] -> Maybe MonoKind
    compXtorKinds [] = Nothing 
    compXtorKinds [mk] = Just mk
    compXtorKinds (xtor1:xtor2:rst) = if xtor1==xtor2 then compXtorKinds (xtor2:rst) else Nothing
annotTy (RST.TyCodata loc pol xtors) = do 
  let xtnms = map RST.sig_name xtors
  xtorKinds <- mapM lookupXtorKind xtnms
  let allEq = compXtorKinds (map fst xtorKinds)
  case allEq of 
    Nothing -> throwOtherError loc ["Not all xtors have the same return kind"]
    Just mk -> do 
      xtors' <- mapM annotXtor xtors
      return $ TST.TyCodata loc pol mk xtors' 
  where 
    compXtorKinds :: [MonoKind] -> Maybe MonoKind
    compXtorKinds [] = Nothing 
    compXtorKinds [mk] = Just mk
    compXtorKinds (xtor1:xtor2:rst) = if xtor1==xtor2 then compXtorKinds (xtor2:rst) else Nothing
annotTy (RST.TyDataRefined loc pol tyn xtors) =  do 
  xtors' <- mapM annotXtor xtors
  tyn' <- gets declTyName
  if tyn == tyn' then do
    polyknd <- gets declKind
    return $ TST.TyDataRefined loc pol (CBox $ returnKind polyknd) tyn xtors' 
  else do 
    decl <- lookupTypeName loc tyn
    return $ TST.TyDataRefined loc pol (CBox $ returnKind $ TST.data_kind decl) tyn xtors' 
annotTy (RST.TyCodataRefined loc pol tyn xtors) = do 
  xtors' <- mapM annotXtor xtors
  tyn' <- gets declTyName
  if tyn == tyn' then do 
    polyknd <- gets declKind
    return $ TST.TyCodataRefined loc pol (CBox $ returnKind polyknd) tyn xtors'
  else do
    decl <- lookupTypeName loc tyn
    return $ TST.TyCodataRefined loc pol (CBox $ returnKind (TST.data_kind decl)) tyn xtors'
annotTy (RST.TyNominal loc pol tyn vartys) = do 
  tyn' <- gets declTyName
  vartys' <- annotVarTys vartys
  if tyn == tyn' then do
    polyknd <- gets declKind
    return $ TST.TyNominal loc pol (CBox $ returnKind polyknd) tyn vartys' 
  else do
    decl <- lookupTypeName loc tyn
    return $ TST.TyNominal loc pol (CBox $ returnKind (TST.data_kind decl)) tyn vartys' 
annotTy (RST.TySyn loc pol tyn ty) =  do 
  ty' <- annotTy ty
  return $ TST.TySyn loc pol tyn ty'
annotTy (RST.TyBot loc) = do TST.TyBot loc . KindVar <$> newDeclKVar
annotTy (RST.TyTop loc) = do TST.TyTop loc . KindVar <$> newDeclKVar
annotTy (RST.TyUnion loc ty1 ty2) = do 
  ty1' <- annotTy ty1 
  ty2' <- annotTy ty2
  let knd = TST.getKind ty1' 
  if knd == TST.getKind ty2' then 
    return $ TST.TyUnion loc knd ty1' ty2'
  else 
    throwOtherError loc ["Kinds of " <> T.pack ( show ty1' ) <> " and " <> T.pack ( show ty2' ) <> " in union do not match"]

annotTy (RST.TyInter loc ty1 ty2) = do 
  ty1' <- annotTy ty1 
  ty2' <- annotTy ty2
  let knd = TST.getKind ty1' 
  if knd == TST.getKind ty2' then 
    return $ TST.TyInter loc knd ty1' ty2'
  else 
    throwOtherError loc ["Kinds of " <> T.pack ( show ty1' ) <> " and " <> T.pack ( show ty2' ) <> " in intersection do not match"]
annotTy (RST.TyRec loc pol tv ty) = do 
  kv <- newDeclKVar
  addRecVar tv (KindVar kv)
  ty' <- annotTy ty
  return $ TST.TyRec loc pol tv ty' 
annotTy (RST.TyI64 loc pol) = return $ TST.TyI64 loc pol
annotTy (RST.TyF64 loc pol) = return $ TST.TyF64 loc pol
annotTy (RST.TyChar loc pol) = return $ TST.TyChar loc pol
annotTy (RST.TyString loc pol) = return $ TST.TyString loc pol
annotTy (RST.TyFlipPol pol ty) = do 
  ty' <- annotTy ty 
  return $ TST.TyFlipPol pol ty'


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
  data_refinement_empty = empt,
  data_refinement_full = ful,
  data_kind = polyknd,
  data_xtors = xtors,
  data_xtors_refined = xtorsref
  } = do
    emptPos <- annotTy (fst empt)
    emptNeg <- annotTy (snd empt)
    fulPos <- annotTy (fst ful) 
    fulNeg <- annotTy (snd ful)
    xtorsPos <- mapM annotXtor (fst xtors)
    xtorsNeg <- mapM annotXtor (snd xtors)
    xtorsRefPos <- mapM annotXtor (fst xtorsref)
    xtorsRefNeg <- mapM annotXtor (snd xtorsref)
    return TST.RefinementDecl {
      data_loc = loc,
      data_doc = doc,
      data_name = tyn,
      data_polarity = pol ,
      data_refinement_empty = (emptPos, emptNeg), 
      data_refinement_full = (fulPos, fulNeg), 
      data_kind = polyknd,
      data_xtors = (xtorsPos, xtorsNeg),
      data_xtors_refined = (xtorsRefPos, xtorsRefNeg) 
      }

--------------------------------------------------------------------------------------------
-- checking Kinds
--------------------------------------------------------------------------------------------

annotateInstDecl ::  (RST.Typ RST.Pos, RST.Typ RST.Neg) -> GenM (TST.Typ RST.Pos, TST.Typ RST.Neg)
annotateInstDecl (ty1, ty2) = do 
  ty1' <- annotateTyp ty1
  ty2' <- annotateTyp ty2
  return (ty1', ty2')

annotateMaybeTypeScheme ::  Maybe (RST.TypeScheme pol) -> GenM (Maybe (TST.TypeScheme pol))
annotateMaybeTypeScheme Nothing = return Nothing 
annotateMaybeTypeScheme (Just ty) = do
  ty' <- annotateTypeScheme ty 
  return (Just ty')

annotateTypeScheme ::  RST.TypeScheme pol -> GenM (TST.TypeScheme pol)
annotateTypeScheme RST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty} = do
  ty' <- annotateTyp ty
  return TST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty'}

annotateVariantType ::  RST.VariantType pol -> GenM (TST.VariantType pol)
annotateVariantType (RST.CovariantType ty) = TST.CovariantType <$> annotateTyp ty
annotateVariantType (RST.ContravariantType ty) = TST.ContravariantType <$> annotateTyp ty

annotatePrdCnsType ::  RST.PrdCnsType pol -> GenM (TST.PrdCnsType pol)
annotatePrdCnsType (RST.PrdCnsType rep ty) = do 
  ty' <- annotateTyp ty
  return (TST.PrdCnsType rep ty')

annotateLinearContext ::  RST.LinearContext pol -> GenM (TST.LinearContext pol)
annotateLinearContext ctxt = do mapM annotatePrdCnsType ctxt

  
annotateXtorSig ::  RST.XtorSig pol -> GenM (TST.XtorSig pol)
annotateXtorSig RST.MkXtorSig { sig_name = nm, sig_args = ctxt } = do 
  ctxt' <- annotateLinearContext ctxt 
  return (TST.MkXtorSig {sig_name = nm, sig_args = ctxt' })

annotateTyp ::  RST.Typ pol -> GenM (TST.Typ pol)
annotateTyp (RST.TySkolemVar loc pol tv) = do
  skMap <- gets usedSkolemVars
  case M.lookup tv skMap of 
    Nothing -> do
      kv <- newKVar
      let newM = M.insert tv (KindVar kv) skMap
      modify (\gs@GenerateState{} -> gs { usedSkolemVars = newM })
      return (TST.TySkolemVar loc pol (KindVar kv) tv)
    Just mk -> return (TST.TySkolemVar loc pol mk tv)

annotateTyp (RST.TyUniVar loc pol tv) = do 
  uniMap <- gets usedUniVars
  case M.lookup tv uniMap of 
    Nothing -> do
      kv <- newKVar
      let newM = M.insert tv (KindVar kv) uniMap
      modify (\gs@GenerateState{} -> gs { usedUniVars = newM })
      return (TST.TyUniVar loc pol (KindVar kv) tv)
    Just mk -> return (TST.TyUniVar loc pol mk tv)

annotateTyp (RST.TyRecVar loc pol rv) = do
  rvMap <- gets usedRecVars
  case M.lookup rv rvMap of 
    Nothing -> do
      kv <- newKVar 
      let newM = M.insert rv (KindVar kv) rvMap
      modify (\gs@GenerateState{} -> gs { usedRecVars = newM })
      return (TST.TyRecVar loc pol (KindVar kv) rv)
    Just mk -> return (TST.TyRecVar loc pol mk rv)

annotateKind (RST.TyData loc pol xtors) = do 
  xtors' <- mapM annotateXtorSig xtors
  knd <- getXtorKinds loc xtors'
  return (TST.TyData loc pol knd xtors')

annotateTyp (RST.TyCodata loc pol xtors) = do 
  knd <- getXtorKinds loc xtors
  xtors' <- mapM annotateXtorSig xtors
  knd <- getXtorKinds loc xtors'
  return (TST.TyCodata loc pol knd xtors')

annotateTyp (RST.TyDataRefined loc pol tyn xtors) = do 
  xtors' <- mapM annotateXtorSig xtors
  (knd,argknds) <- getTyNameKind loc tyn
  -- make sure all applied constructor arguments match defined constructor arguments 
  forM_ xtors' (\x -> genArgConstrs loc (TST.sig_name x) argknds (TST.sig_args x)) 
  return (TST.TyDataRefined loc pol knd tyn xtors')

annotateTyp (RST.TyCodataRefined loc pol tyn xtors) = do
  xtors' <- mapM annotateXtorSig xtors
  (knd, argknds) <- getTyNameKind loc tyn
  -- make sure all applied constructor arguments match defined constructor arguments 
  forM_ xtors' (\x -> genArgConstrs loc (TST.sig_name x) argknds (TST.sig_args x)) 
  return (TST.TyCodataRefined loc pol knd tyn xtors')

annotateTyp (RST.TyNominal loc pol tyn vartys) = do
  vartys' <- mapM annotateVariantType vartys
  (knd,argknds) <- getTyNameKind loc tyn
  -- make sure all applied constructor arguments match defined constructor arguments 
  checkVartyKinds loc vartys' argknds 
  return (TST.TyNominal loc pol knd tyn vartys')
  where 
    checkVartyKinds :: Loc -> [TST.VariantType pol] -> [MonoKind] -> GenM() 
    checkVartyKinds _ [] [] = return ()
    checkVartyKinds loc (_:_) [] = throwOtherError loc ["Too many arguments for nominal type " <> ppPrint tyn]
    checkVartyKinds loc [] (_:_) = throwOtherError loc ["Too few arguments for nominal type " <> ppPrint tyn]
    checkVartyKinds loc (fst:rst) (fst':rst') = do 
      addConstraint (KindEq KindConstraint (getKind fst) fst')
      checkVartyKinds loc rst rst'

annotateTyp (RST.TySyn loc pol tn ty) = do 
  ty' <- annotateTyp ty 
  return (TST.TySyn loc pol tn ty')

annotateKind (RST.TyTop loc) = do TST.TyTop loc . KindVar <$> newKVar
annotateTyp (RST.TyBot loc) = TST.TyBot loc . KindVar <$> newKVar

annotateTyp (RST.TyTop loc) = TST.TyTop loc . KindVar <$> newKVar

annotateTyp (RST.TyUnion loc ty1 ty2) = do 
  ty1' <- annotateTyp ty1
  ty2' <- annotateTyp ty2
  kv <- newKVar 
  -- Union Type needs to have the same kind as its arguments
  addConstraint $ KindEq KindConstraint (KindVar kv) (getKind ty2')
  addConstraint $ KindEq KindConstraint (KindVar kv) (getKind ty1')
  return (TST.TyUnion loc (KindVar kv) ty1' ty2')
  
annotateTyp (RST.TyInter loc ty1 ty2) = do
  ty1' <- annotateTyp ty1
  ty2' <- annotateTyp ty2
  kv <- newKVar 
  -- Intersection Type needs to have the same kind as its arguments
  addConstraint $ KindEq KindConstraint (KindVar kv) (getKind ty2')
  addConstraint $ KindEq KindConstraint (KindVar kv) (getKind ty1')
  return (TST.TyInter loc (KindVar kv) ty1' ty2')
  
annotateTyp (RST.TyRec loc pol rv ty) = do
  ty' <- annotateTyp ty
  return (TST.TyRec loc pol rv ty')

annotateTyp (RST.TyI64 loc pol) = return (TST.TyI64 loc pol)
annotateTyp (RST.TyF64 loc pol) = return (TST.TyF64 loc pol)
annotateTyp (RST.TyChar loc pol) = return (TST.TyChar loc pol)
annotateTyp (RST.TyString loc pol) = return(TST.TyString loc pol)

annotateTyp (RST.TyFlipPol pol ty) = do 
  ty' <- annotateTyp ty
  return (TST.TyFlipPol pol ty')


