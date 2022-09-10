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

import Control.Monad.State
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Bifunctor (bimap)


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
-- we can't use the environment here, as the results are inserted into the environment

-- only temporary, will be removed 
defaultKind :: MonoKind
defaultKind = CBox CBV

annotXtor :: RST.XtorSig pol -> TST.XtorSig pol
annotXtor (RST.MkXtorSig nm ctxt) = TST.MkXtorSig nm (annotCtxt ctxt)

annotCtxt :: RST.LinearContext pol -> TST.LinearContext pol
annotCtxt [] = []
annotCtxt (RST.PrdCnsType pc ty:rst) = TST.PrdCnsType  pc (annotTy ty) : annotCtxt rst

annotVarTys :: [RST.VariantType pol] -> [TST.VariantType pol]
annotVarTys [] = [] 
annotVarTys (RST.CovariantType ty:rst) = TST.CovariantType (annotTy ty) : annotVarTys rst
annotVarTys (RST.ContravariantType ty:rst) = TST.ContravariantType (annotTy ty) : annotVarTys rst


annotTy :: RST.Typ pol -> TST.Typ pol
annotTy (RST.TySkolemVar loc pol tv) = TST.TySkolemVar loc pol defaultKind tv 
annotTy (RST.TyUniVar loc pol tv) = TST.TyUniVar loc pol defaultKind tv
annotTy (RST.TyRecVar loc pol tv) = TST.TyRecVar loc pol defaultKind tv
annotTy (RST.TyData loc pol xtors) = TST.TyData loc pol defaultKind (map annotXtor xtors)
annotTy (RST.TyCodata loc pol xtors) = TST.TyCodata loc pol defaultKind (map annotXtor xtors)
annotTy (RST.TyDataRefined loc pol tyn xtors) = TST.TyDataRefined loc pol defaultKind tyn (map annotXtor xtors)
annotTy (RST.TyCodataRefined loc pol tyn xtors) = TST.TyCodataRefined loc pol defaultKind tyn (map annotXtor xtors)
annotTy (RST.TyNominal loc pol tyn vartys) = TST.TyNominal loc pol defaultKind tyn (annotVarTys vartys)
annotTy (RST.TySyn loc pol tyn ty) = TST.TySyn loc pol tyn (annotTy ty)
annotTy (RST.TyBot loc) = TST.TyBot loc defaultKind
annotTy (RST.TyTop loc) =  TST.TyTop loc defaultKind
annotTy (RST.TyUnion loc ty1 ty2) = TST.TyUnion loc defaultKind (annotTy ty1) (annotTy ty2)
annotTy (RST.TyInter loc ty1 ty2) = TST.TyInter loc defaultKind (annotTy ty1) (annotTy ty2)
annotTy (RST.TyRec loc pol tv ty) = TST.TyRec loc pol tv (annotTy ty)
annotTy (RST.TyI64 loc pol) = TST.TyI64 loc pol
annotTy (RST.TyF64 loc pol) = TST.TyF64 loc pol
annotTy (RST.TyChar loc pol) = TST.TyChar loc pol
annotTy (RST.TyString loc pol) = TST.TyString loc pol
annotTy (RST.TyFlipPol pol ty) = TST.TyFlipPol pol (annotTy ty)


annotateDataDecl :: RST.DataDecl -> TST.DataDecl 
annotateDataDecl RST.NominalDecl {
  data_loc = loc, 
  data_doc = doc,
  data_name = tyn,
  data_polarity = pol,
  data_kind = polyknd,
  data_xtors = xtors 
  } = do
  let xtors' = Data.Bifunctor.bimap (map annotXtor) (map annotXtor) xtors
  TST.NominalDecl { 
    data_loc = loc, 
    data_doc = doc,
    data_name = tyn,
    data_polarity = pol,
    data_kind = polyknd,
    data_xtors = xtors'
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
  } =  do
  let empt' = Data.Bifunctor.bimap annotTy annotTy empt
  let ful' = Data.Bifunctor.bimap annotTy annotTy ful
  let xtors' = Data.Bifunctor.bimap (map annotXtor) (map annotXtor) xtors
  let xtorsref' = Data.Bifunctor.bimap (map annotXtor) (map annotXtor) xtorsref
  TST.RefinementDecl {
    data_loc = loc, 
    data_doc = doc,
    data_name = tyn,
    data_polarity = pol ,
    data_refinement_empty = empt',
    data_refinement_full = ful',
    data_kind = polyknd,
    data_xtors = xtors',
    data_xtors_refined = xtorsref' 
  }

--------------------------------------------------------------------------------------------
-- checking Kinds
--------------------------------------------------------------------------------------------

annotateInstDecl ::  (RST.Typ RST.Pos, RST.Typ RST.Neg) -> GenM (TST.Typ RST.Pos, TST.Typ RST.Neg)
annotateInstDecl (ty1, ty2) = do 
  ty1' <- annotateKind ty1
  ty2' <- annotateKind ty2
  return (ty1', ty2')

annotateMaybeTypeScheme ::  Maybe (RST.TypeScheme pol) -> GenM (Maybe (TST.TypeScheme pol))
annotateMaybeTypeScheme Nothing = return Nothing 
annotateMaybeTypeScheme (Just ty) = do
  ty' <- annotateTypeScheme ty 
  return (Just ty')

annotateTypeScheme ::  RST.TypeScheme pol -> GenM (TST.TypeScheme pol)
annotateTypeScheme RST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty} = do
  ty' <- annotateKind ty
  return TST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty'}

annotateVariantType ::  RST.VariantType pol -> GenM (TST.VariantType pol)
annotateVariantType (RST.CovariantType ty) = TST.CovariantType <$> annotateKind ty
annotateVariantType (RST.ContravariantType ty) = TST.ContravariantType <$> annotateKind ty

annotatePrdCnsType ::  RST.PrdCnsType pol -> GenM (TST.PrdCnsType pol)
annotatePrdCnsType (RST.PrdCnsType rep ty) = do 
  ty' <- annotateKind ty
  return (TST.PrdCnsType rep ty')

annotateLinearContext ::  RST.LinearContext pol -> GenM (TST.LinearContext pol)
annotateLinearContext = mapM annotatePrdCnsType

annotateXtorSig ::  RST.XtorSig pol -> GenM (TST.XtorSig pol)
annotateXtorSig RST.MkXtorSig { sig_name = nm, sig_args = ctxt } = do 
  ctxt' <- annotateLinearContext ctxt 
  return (TST.MkXtorSig {sig_name = nm, sig_args = ctxt' })

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
  xtors' <- mapM annotateXtorSig xtors
  return (TST.TyData loc pol knd xtors')

annotateKind (RST.TyCodata loc pol xtors) = do 
  knd <- getXtorKinds loc xtors
  xtors' <- mapM annotateXtorSig xtors
  return (TST.TyCodata loc pol knd xtors')

annotateKind (RST.TyDataRefined loc pol tyn xtors) = do 
  xtors' <- mapM annotateXtorSig xtors
  knd <- getTyNameKind loc tyn
  return (TST.TyDataRefined loc pol knd tyn xtors')

annotateKind (RST.TyCodataRefined loc pol tyn xtors) = do
  xtors' <- mapM annotateXtorSig xtors
  knd <- getTyNameKind loc tyn
  return (TST.TyCodataRefined loc pol knd tyn xtors')

annotateKind (RST.TyNominal loc pol tyn vartys) = do
  vartys' <- mapM annotateVariantType vartys
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


