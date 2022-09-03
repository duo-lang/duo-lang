module TypeInference.GenerateConstraints.Kinds where

import Syntax.RST.Program qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.TST.Types qualified as TST
import Syntax.CST.Kinds
import Syntax.CST.Names 
import Lookup
import Errors
import Driver.Environment
import Loc
import Pretty.Pretty
import TypeInference.GenerateConstraints.Definition

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import Data.List.NonEmpty (NonEmpty)
import Data.Map qualified as M
import Data.Text qualified as T

--------------------------------------------------------------------------------------------
-- Kind Inference Monad 
--------------------------------------------------------------------------------------------
type KindReader m = (MonadError (NonEmpty Error) m, MonadReader (M.Map ModuleName Environment, GenerateReader) m, MonadState GenerateState m)

--------------------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------------------
getXtorKinds :: KindReader m => Loc -> [RST.XtorSig pol] -> m MonoKind
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

getTyNameKind :: KindReader m => Loc -> RnTypeName -> m MonoKind
getTyNameKind loc tyn = do
  decl <- lookupTypeName loc tyn
  getKindDecl decl
  
getKindDecl :: KindReader m => RST.DataDecl -> m MonoKind
getKindDecl decl = do
  let polyknd = RST.data_kind decl
  return (CBox (returnKind polyknd))

newKVar :: KindReader  m => m KVar
newKVar = do
  kvCnt <- gets kVarCount
  modify (\gs@GenerateState{} -> gs { kVarCount = kvCnt + 1 })
  return (MkKVar (T.pack ("kv" <> show kvCnt)))

--------------------------------------------------------------------------------------------
-- checking Kinds
--------------------------------------------------------------------------------------------

annotateInstDecl :: KindReader m => (RST.Typ RST.Pos, RST.Typ RST.Neg) -> m (TST.Typ RST.Pos, TST.Typ RST.Neg)
annotateInstDecl (ty1, ty2) = do 
  ty1' <- annotateKind ty1
  ty2' <- annotateKind ty2
  return (ty1', ty2')

annotateMaybeTypeScheme :: KindReader m => Maybe (RST.TypeScheme pol) -> m (Maybe (TST.TypeScheme pol))
annotateMaybeTypeScheme Nothing = return Nothing 
annotateMaybeTypeScheme (Just ty) = do
  ty' <- annotateTypeScheme ty 
  return (Just ty')

annotateTypeScheme :: KindReader m => RST.TypeScheme pol -> m (TST.TypeScheme pol)
annotateTypeScheme RST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty} = do
  ty' <- annotateKind ty
  return TST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty'}

annotateVariantType :: KindReader m => RST.VariantType pol -> m (TST.VariantType pol)
annotateVariantType (RST.CovariantType ty) = TST.CovariantType <$> annotateKind ty
annotateVariantType (RST.ContravariantType ty) = TST.ContravariantType <$> annotateKind ty

annotatePrdCnsType :: KindReader m => RST.PrdCnsType pol -> m (TST.PrdCnsType pol)
annotatePrdCnsType (RST.PrdCnsType rep ty) = do 
  ty' <- annotateKind ty
  return (TST.PrdCnsType rep ty')

annotateLinearContext :: KindReader m => RST.LinearContext pol -> m (TST.LinearContext pol)
annotateLinearContext = mapM annotatePrdCnsType

annotateXtorSig :: KindReader m => RST.XtorSig pol -> m (TST.XtorSig pol)
annotateXtorSig RST.MkXtorSig { sig_name = nm, sig_args = ctxt } = do 
  ctxt' <- annotateLinearContext ctxt 
  return (TST.MkXtorSig {sig_name = nm, sig_args = ctxt' })

annotateKind :: KindReader m => RST.Typ pol -> m (TST.Typ pol)
annotateKind (RST.TySkolemVar loc pol tv) = do
  kv <- newKVar
  return (TST.TySkolemVar loc pol (KindVar kv) tv)

annotateKind (RST.TyUniVar loc pol tv) = do 
  kv <- newKVar 
  return (TST.TyUniVar loc pol (KindVar kv) tv)

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

annotateKind (RST.TyBot loc) = do TST.TyBot loc . KindVar <$> newKVar

annotateKind (RST.TyTop loc) = do TST.TyTop loc . KindVar <$> newKVar

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


