module TypeInference.GenerateConstraints.Kinds where

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
  let polyKnd = RST.data_kind decl
  let argKnds = map (\(_,_,x) -> x) (kindArgs polyKnd)
  return (CBox (returnKind polyKnd), argKnds)

getKindDecl :: RST.DataDecl -> GenM MonoKind 
getKindDecl = return . CBox . returnKind . RST.data_kind

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
annotateLinearContext ctxt = do mapM annotatePrdCnsType ctxt

  
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
  xtors' <- mapM annotateXtorSig xtors
  knd <- getXtorKinds loc xtors'
  return (TST.TyData loc pol knd xtors')

annotateKind (RST.TyCodata loc pol xtors) = do 
  xtors' <- mapM annotateXtorSig xtors
  knd <- getXtorKinds loc xtors'
  return (TST.TyCodata loc pol knd xtors')

annotateKind (RST.TyDataRefined loc pol tyn xtors) = do 
  xtors' <- mapM annotateXtorSig xtors
  (knd,argknds) <- getTyNameKind loc tyn
  -- make sure all applied constructor arguments match defined constructor arguments 
  forM_ xtors' (\x -> genArgConstrs loc (TST.sig_name x) argknds (TST.sig_args x)) 
  return (TST.TyDataRefined loc pol knd tyn xtors')

annotateKind (RST.TyCodataRefined loc pol tyn xtors) = do
  xtors' <- mapM annotateXtorSig xtors
  (knd, argknds) <- getTyNameKind loc tyn
  -- make sure all applied constructor arguments match defined constructor arguments 
  forM_ xtors' (\x -> genArgConstrs loc (TST.sig_name x) argknds (TST.sig_args x)) 
  return (TST.TyCodataRefined loc pol knd tyn xtors')

annotateKind (RST.TyNominal loc pol tyn vartys) = do
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

annotateKind (RST.TySyn loc pol tn ty) = do 
  ty' <- annotateKind ty 
  return (TST.TySyn loc pol tn ty')

annotateKind (RST.TyBot loc) = do TST.TyBot loc . KindVar <$> newKVar

annotateKind (RST.TyTop loc) = do TST.TyTop loc . KindVar <$> newKVar

annotateKind (RST.TyUnion loc ty1 ty2) = do 
  ty1' <- annotateKind ty1
  ty2' <- annotateKind ty2
  kv <- newKVar 
  -- Union Type needs to have the same kind as its arguments
  addConstraint $ KindEq KindConstraint (KindVar kv) (getKind ty2')
  addConstraint $ KindEq KindConstraint (KindVar kv) (getKind ty1')
  return (TST.TyUnion loc (KindVar kv) ty1' ty2')
  
annotateKind (RST.TyInter loc ty1 ty2) = do
  ty1' <- annotateKind ty1
  ty2' <- annotateKind ty2
  kv <- newKVar 
  -- Intersection Type needs to have the same kind as its arguments
  addConstraint $ KindEq KindConstraint (KindVar kv) (getKind ty2')
  addConstraint $ KindEq KindConstraint (KindVar kv) (getKind ty1')
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


