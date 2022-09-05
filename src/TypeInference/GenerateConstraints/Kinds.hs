module TypeInference.GenerateConstraints.Kinds where

import Syntax.RST.Program qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.TST.Types qualified as TST
import Syntax.TST.Types (getKind)
import Syntax.CST.Kinds
import Syntax.CST.Names 
import Lookup
import Errors
import Loc
import TypeInference.Constraints
import TypeInference.GenerateConstraints.Definition

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
  addConstraint $ KindEq (ReadConstraint loc) knd knd'
  return knd

getTyNameKind ::  Loc -> RnTypeName -> GenM MonoKind
getTyNameKind loc tyn = do
  decl <- lookupTypeName loc tyn
  getKindDecl loc decl
  
getKindDecl ::  Loc -> RST.DataDecl -> GenM MonoKind
getKindDecl loc decl = do
  let polyknd = RST.data_kind decl
  let retknd = CBox (returnKind polyknd)
  let argknds = map (\(_,_,x) -> x) (kindArgs polyknd)
  let constrs = map (KindEq (ReadConstraint loc) retknd) argknds
  mapM_ addConstraint constrs
  return retknd

newKVar :: GenM KVar
newKVar = do
  kvCnt <- gets kVarCount
  let kVar = MkKVar (T.pack ("kv" <> show kvCnt))
  modify (\gs@GenerateState{} -> gs { kVarCount = kvCnt + 1 })
  modify (\gs@GenerateState{ constraintSet = cs@ConstraintSet { cs_kvars } } ->
            gs { constraintSet = cs {cs_kvars = cs_kvars ++ [kVar] } })
  return kVar 

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
annotateLinearContext ctxt = do
  ctxt' <- mapM annotatePrdCnsType ctxt
  let knds = map getKind ctxt'
  let constrs = genArgConstrs knds 
  mapM_ addConstraint constrs
  return ctxt'
  where 
    genArgConstrs [] = []
    genArgConstrs [_] = []
    genArgConstrs (fst:snd:rst) = KindEq (ReadConstraint defaultLoc) fst snd:genArgConstrs (snd:rst)

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
  addConstraint $ KindEq (ReadConstraint loc) (KindVar kv) (getKind ty2')
  addConstraint $ KindEq (ReadConstraint loc) (KindVar kv) (getKind ty1')
  return (TST.TyUnion loc (KindVar kv) ty1' ty2')
  
annotateKind (RST.TyInter loc ty1 ty2) = do
  ty1' <- annotateKind ty1
  ty2' <- annotateKind ty2
  kv <- newKVar 
  addConstraint $ KindEq (ReadConstraint loc) (KindVar kv) (getKind ty2')
  addConstraint $ KindEq (ReadConstraint loc) (KindVar kv) (getKind ty1')
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


