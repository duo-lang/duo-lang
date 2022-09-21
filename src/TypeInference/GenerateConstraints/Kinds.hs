{-# LANGUAGE FunctionalDependencies #-}

module TypeInference.GenerateConstraints.Kinds where

import Syntax.TST.Program qualified as TST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.TST.Types qualified as TST
import Syntax.CST.Kinds
import Syntax.CST.Names 
import Lookup
import Errors
import Loc
import Pretty.Pretty
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
getXtorKinds :: Loc -> [RST.XtorSig pol] -> GenM MonoKind
getXtorKinds loc [] = throwSolverError loc ["Can't find kinds of empty List of Xtors"]
getXtorKinds _ [xtor] = do 
  let nm = RST.sig_name xtor
  lookupXtorKind nm
getXtorKinds loc (fst:rst) = do
  let nm = RST.sig_name fst
  knd <- lookupXtorKind nm
  knd' <- getXtorKinds loc rst
  if knd == knd' then
    return knd 
  else 
    throwSolverError loc ["Kinds ", ppPrint knd , " and ", ppPrint knd', "of constructors do not match"]

getTyNameKind ::  Loc -> RnTypeName -> GenM MonoKind
getTyNameKind loc tyn = do
  decl <- lookupTypeName loc tyn
  getKindDecl decl
  
getKindDecl ::  TST.DataDecl -> GenM MonoKind
getKindDecl decl = do
  let polyknd = TST.data_kind decl
  return (CBox (returnKind polyknd))

newKVar :: GenM KVar
newKVar = do
  kvCnt <- gets kVarCount
  modify (\gs@GenerateState{} -> gs { kVarCount = kvCnt + 1 })
  return (MkKVar (T.pack ("kv" <> show kvCnt)))

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
annotXtor (RST.MkXtorSig nm ctxt) =
  TST.MkXtorSig nm <$> mapM annotPrdCns ctxt

annotPrdCns :: RST.PrdCnsType pol -> DataDeclM (TST.PrdCnsType pol)
annotPrdCns (RST.PrdCnsType pc ty) = 
  TST.PrdCnsType pc <$> annotTy ty

annotVarTy :: RST.VariantType pol -> DataDeclM (TST.VariantType pol)
annotVarTy (RST.CovariantType ty) =
  TST.CovariantType <$> annotTy ty 
annotVarTy (RST.ContravariantType ty) =
  TST.ContravariantType <$> annotTy ty 


getKindSkolem :: PolyKind -> SkolemTVar -> MonoKind
getKindSkolem polyknd = searchKindArgs (kindArgs polyknd)
  where 
    searchKindArgs :: [(Variance, SkolemTVar, MonoKind)] -> SkolemTVar -> MonoKind
    searchKindArgs [] _ = error "Skolem Variable not found in argument types of polykind"
    searchKindArgs ((_,tv,mk):rst) tv' = if tv == tv' then mk else searchKindArgs rst tv'

-- only recvars, bottom and top can contain kvars
removeKVars :: TST.Typ pol -> DataDeclM (TST.Typ pol)
-- already correctly annotated
removeKVars sv@TST.TySkolemVar{}          = return sv
-- should neve appear
removeKVars uv@TST.TyUniVar{}             = return uv
removeKVars rv@TST.TyRecVar{}             = return rv                            -- TODO -- always gets kvar (
removeKVars tyd@TST.TyData{}              = return tyd                           -- TODO -- xtors are annotated (actual kind always inhabited)
removeKVars tycd@TST.TyCodata{}           = return tycd                          -- TODO -- xtors are annotated (actual kind always inhabited) 
removeKVars tydr@TST.TyDataRefined{}      = return tydr                          -- TODO -- xtors are annotated 
removeKVars tycdr@TST.TyCodataRefined{}   = return tycdr                         -- TODO -- xtors are annotated 
removeKVars tyn@TST.TyNominal{}           = return tyn                           -- TODO -- vartys are annotated
-- only the contained type has to be checked
removeKVars (TST.TySyn loc pol tyn ty)    = do 
  ty' <- removeKVars ty
  return $ TST.TySyn loc pol tyn ty'
removeKVars bot@TST.TyBot{}               = return bot                           -- TODO -- always gets kvar 
removeKVars top@TST.TyTop{}               = return top                           -- TODO -- always gets kvar
removeKVars (TST.TyUnion loc knd ty1 ty2) = return (TST.TyUnion loc knd ty1 ty2) -- TODO -- ty1 and ty2 may contain kvars
removeKVars (TST.TyInter loc knd ty1 ty2) = return (TST.TyInter loc knd ty1 ty2) -- TODO -- ty1 and ty2 may contain kvars
removeKVars tr@TST.TyRec{}                = return tr                            -- TODO -- recursive type and recvar may contain kvars
-- primitive types don't contain a type
removeKVars i64@TST.TyI64{}               = return i64
removeKVars f64@TST.TyF64{}               = return f64
removeKVars ch@TST.TyChar{}               = return ch
removeKVars str@TST.TyString{}            = return str
-- only the contained type needs to be checked
removeKVars (TST.TyFlipPol pol ty)        = do 
  ty' <- removeKVars ty
  return $ TST.TyFlipPol pol ty'


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
  let allEq = compXtorKinds xtorKinds  
  case allEq of 
    Nothing -> throwOtherError loc ["Not all xtors have the same return kind"]
    Just mk -> do 
      xtors' <- mapM (\x -> lookupXtorSig loc x pol) xtnms
      return $ TST.TyData loc pol mk xtors' 
  where 
    compXtorKinds :: [MonoKind] -> Maybe MonoKind
    compXtorKinds [] = Nothing 
    compXtorKinds [mk] = Just mk
    compXtorKinds (xtor1:xtor2:rst) = if xtor1==xtor2 then compXtorKinds (xtor2:rst) else Nothing
annotTy (RST.TyCodata loc pol xtors) = do 
  let xtnms = map RST.sig_name xtors
  xtorKinds <- mapM lookupXtorKind xtnms
  let allEq = compXtorKinds xtorKinds  
  case allEq of 
    Nothing -> throwOtherError loc ["Not all xtors have the same return kind"]
    Just mk -> do 
      xtors' <- mapM (\x -> lookupXtorSig loc x (RST.flipPolarityRep pol)) xtnms
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
  vartys' <- mapM annotVarTy vartys
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
  data_xtors = (xtorsPos, xtorsNeg)
  } =do 
    xtorsPos' <- mapM annotXtor xtorsPos
    xtorsNeg' <- mapM annotXtor xtorsNeg
    return TST.NominalDecl { 
        data_loc = loc, 
        data_doc = doc,
        data_name = tyn,
        data_polarity = pol,
        data_kind = polyknd,
        data_xtors = (xtorsPos', xtorsNeg') 
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

class AnnotateKind a b | a -> b where
  annotateKind :: a -> GenM b

instance AnnotateKind  (RST.Typ RST.Pos, RST.Typ RST.Neg) (TST.Typ RST.Pos, TST.Typ RST.Neg) where
  annotateKind ::  (RST.Typ RST.Pos, RST.Typ RST.Neg) -> GenM (TST.Typ RST.Pos, TST.Typ RST.Neg)
  annotateKind (ty1, ty2) = do 
    ty1' <- annotateKind ty1
    ty2' <- annotateKind ty2
    return (ty1', ty2')

annotateMaybeTypeScheme ::  Maybe (RST.TypeScheme pol) -> GenM (Maybe (TST.TypeScheme pol))
annotateMaybeTypeScheme Nothing = return Nothing 
annotateMaybeTypeScheme (Just ty) = do
  ty' <- annotateKind ty 
  return (Just ty')

instance AnnotateKind (RST.TypeScheme pol) (TST.TypeScheme pol) where
  annotateKind ::  RST.TypeScheme pol -> GenM (TST.TypeScheme pol)
  annotateKind RST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty} = do
    ty' <- annotateKind ty
    return TST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty'}

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
    skMap <- gets usedSkolemVars
    case M.lookup tv skMap of 
      Nothing -> do
        kv <- newKVar
        let newM = M.insert tv (KindVar kv) skMap
        modify (\gs@GenerateState{} -> gs { usedSkolemVars = newM })
        return (TST.TySkolemVar loc pol (KindVar kv) tv)
      Just mk -> return (TST.TySkolemVar loc pol mk tv)

  annotateKind (RST.TyUniVar loc pol tv) = do 
    uniMap <- gets usedUniVars
    case M.lookup tv uniMap of 
      Nothing -> do
        kv <- newKVar
        let newM = M.insert tv (KindVar kv) uniMap
        modify (\gs@GenerateState{} -> gs { usedUniVars = newM })
        return (TST.TyUniVar loc pol (KindVar kv) tv)
      Just mk -> return (TST.TyUniVar loc pol mk tv)

  annotateKind (RST.TyRecVar loc pol rv) = do
    rvMap <- gets usedRecVars
    case M.lookup rv rvMap of 
      Nothing -> do
        kv <- newKVar 
        let newM = M.insert rv (KindVar kv) rvMap
        modify (\gs@GenerateState{} -> gs { usedRecVars = newM })
        return (TST.TyRecVar loc pol (KindVar kv) rv)
      Just mk -> return (TST.TyRecVar loc pol mk rv)

  annotateKind (RST.TyData loc pol xtors) = do 
    knd <- getXtorKinds loc xtors 
    xtors' <- mapM annotateKind xtors
    return (TST.TyData loc pol knd xtors')

  annotateKind (RST.TyCodata loc pol xtors) = do 
    knd <- getXtorKinds loc xtors
    xtors' <- mapM annotateKind xtors
    return (TST.TyCodata loc pol knd xtors')

  annotateKind (RST.TyDataRefined loc pol tyn xtors) = do 
    xtors' <- mapM annotateKind xtors
    knd <- getTyNameKind loc tyn
    return (TST.TyDataRefined loc pol knd tyn xtors')

  annotateKind (RST.TyCodataRefined loc pol tyn xtors) = do
    xtors' <- mapM annotateKind xtors
    knd <- getTyNameKind loc tyn
    return (TST.TyCodataRefined loc pol knd tyn xtors')

  annotateKind (RST.TyNominal loc pol tyn vartys) = do
    vartys' <- mapM annotateKind vartys
    knd <- getTyNameKind loc tyn
    return (TST.TyNominal loc pol knd tyn vartys')

  annotateKind (RST.TySyn loc pol tn ty) = do 
    ty' <- annotateKind ty 
    return (TST.TySyn loc pol tn ty')

  annotateKind (RST.TyBot loc) = TST.TyBot loc . KindVar <$> newKVar

  annotateKind (RST.TyTop loc) = TST.TyTop loc . KindVar <$> newKVar

  annotateKind (RST.TyUnion loc ty1 ty2) = do 
    ty1' <- annotateKind ty1
    ty2' <- annotateKind ty2
    kv <- newKVar 
    return (TST.TyUnion loc (KindVar kv) ty1' ty2')
    
  annotateKind (RST.TyInter loc ty1 ty2) = do
    ty1' <- annotateKind ty1
    ty2' <- annotateKind ty2
    kv <- newKVar 
    return (TST.TyInter loc (KindVar kv) ty1' ty2')
    
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


