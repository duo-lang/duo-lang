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

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import Data.List.NonEmpty (NonEmpty)
import Data.Map qualified as M
import Data.Text qualified as T

--------------------------------------------------------------------------------------------
-- Kind Inference Monad 
--------------------------------------------------------------------------------------------
type KindReader a m = (MonadError (NonEmpty Error) m, MonadReader (M.Map ModuleName Environment, a) m) -- , MonadState GenerateState m)

--------------------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------------------
getXtorKinds :: KindReader a m => Loc -> [RST.XtorSig pol] -> m MonoKind
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

getTyNameKind :: KindReader a m => Loc -> RnTypeName -> m MonoKind
getTyNameKind loc tyn = do
  decl <- lookupTypeName loc tyn
  getKindDecl decl
  
getKindDecl :: KindReader a m => RST.DataDecl -> m MonoKind
getKindDecl decl = do
  let polyknd = RST.data_kind decl
  return (CBox (returnKind polyknd))

checkInstDecl :: KindReader a m => (RST.Typ RST.Pos, RST.Typ RST.Neg) -> m (TST.Typ RST.Pos, TST.Typ RST.Neg)
checkInstDecl (ty1, ty2) = do 
  ty1' <- checkKind ty1
  ty2' <- checkKind ty2
  return (ty1', ty2')

checkMaybeTypeScheme :: KindReader a m => Maybe (RST.TypeScheme pol) -> m (Maybe (TST.TypeScheme pol))
checkMaybeTypeScheme Nothing = return Nothing 
checkMaybeTypeScheme (Just ty) = do
  ty' <- checkTypeScheme ty 
  return (Just ty')

checkTypeScheme :: KindReader a m => RST.TypeScheme pol -> m (TST.TypeScheme pol)
checkTypeScheme RST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty} = do
  ty' <- checkKind ty
  return TST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty'}

checkVariantType :: KindReader a m => RST.VariantType pol -> m (TST.VariantType pol)
checkVariantType (RST.CovariantType ty) = TST.CovariantType <$> checkKind ty
checkVariantType (RST.ContravariantType ty) = TST.ContravariantType <$> checkKind ty

checkPrdCnsType :: KindReader a m => RST.PrdCnsType pol -> m (TST.PrdCnsType pol)
checkPrdCnsType (RST.PrdCnsType rep ty) = do 
  ty' <- checkKind ty
  return (TST.PrdCnsType rep ty')

checkLinearContext :: KindReader a m => RST.LinearContext pol -> m (TST.LinearContext pol)
checkLinearContext = mapM checkPrdCnsType

checkXtorSig :: KindReader a m => RST.XtorSig pol -> m (TST.XtorSig pol)
checkXtorSig RST.MkXtorSig { sig_name = nm, sig_args = ctxt } = do 
  ctxt' <- checkLinearContext ctxt 
  return (TST.MkXtorSig {sig_name = nm, sig_args = ctxt' })

checkKind :: KindReader a m => RST.Typ pol -> m (TST.Typ pol)
checkKind (RST.TySkolemVar loc pol tv) = do
  let knd = KindVar (MkKVar (unSkolemTVar tv))
  return (TST.TySkolemVar loc pol knd tv)

checkKind (RST.TyUniVar loc pol tv) = do 
  let knd = KindVar (MkKVar (unUniTVar tv))
  return (TST.TyUniVar loc pol knd tv)

checkKind (RST.TyRecVar loc pol rv) = do
  let knd = KindVar (MkKVar (unRecTVar rv))
  return (TST.TyRecVar loc pol knd rv)

checkKind (RST.TyData loc pol xtors) = do 
  knd <- getXtorKinds loc xtors 
  xtors' <- mapM checkXtorSig xtors
  return (TST.TyData loc pol knd xtors')

checkKind (RST.TyCodata loc pol xtors) = do 
  knd <- getXtorKinds loc xtors
  xtors' <- mapM checkXtorSig xtors
  return (TST.TyCodata loc pol knd xtors')

checkKind (RST.TyDataRefined loc pol tyn xtors) = do 
  xtors' <- mapM checkXtorSig xtors
  knd <- getTyNameKind loc tyn
  return (TST.TyDataRefined loc pol knd tyn xtors')

checkKind (RST.TyCodataRefined loc pol tyn xtors) = do
  xtors' <- mapM checkXtorSig xtors
  knd <- getTyNameKind loc tyn
  return (TST.TyCodataRefined loc pol knd tyn xtors')

checkKind (RST.TyNominal loc pol tyn vartys) = do
  vartys' <- mapM checkVariantType vartys
  knd <- getTyNameKind loc tyn
  return (TST.TyNominal loc pol knd tyn vartys')

checkKind (RST.TySyn loc pol tn ty) = do 
  ty' <- checkKind ty 
  return (TST.TySyn loc pol tn ty')

checkKind (RST.TyBot loc) = return (TST.TyBot loc topbotVar)
checkKind (RST.TyTop loc) = return (TST.TyTop loc topbotVar)

checkKind (RST.TyUnion loc ty1 ty2) = do 
  ty1' <- checkKind ty1
  ty2' <- checkKind ty2
  -- not an optimal name for the kvar, but it should always be unique
  let knd = KindVar (MkKVar (T.pack ("kvUnion" <> show ty1 <> "\\/" <> show ty2)))
  return (TST.TyUnion loc knd ty1' ty2')
  
checkKind (RST.TyInter loc ty1 ty2) = do
  ty1' <- checkKind ty1
  ty2' <- checkKind ty2
  -- not an optimal name for the kvar, but it should always be unique
  let knd = KindVar (MkKVar (T.pack ("kvInter" <> show ty1 <> "/\\" <> show ty2)))
  return (TST.TyInter loc knd ty1' ty2')
  
checkKind (RST.TyRec loc pol rv ty) = do
  ty' <- checkKind ty
  return (TST.TyRec loc pol rv ty')

checkKind (RST.TyI64 loc pol) = return (TST.TyI64 loc pol)
checkKind (RST.TyF64 loc pol) = return (TST.TyF64 loc pol)
checkKind (RST.TyChar loc pol) = return (TST.TyChar loc pol)
checkKind (RST.TyString loc pol) = return(TST.TyString loc pol)

checkKind (RST.TyFlipPol pol ty) = do 
  ty' <- checkKind ty
  return (TST.TyFlipPol pol ty')


