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

import Control.Monad.State
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Bifunctor (bimap)

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

  
getKindDecl ::  TST.DataDecl -> GenM MonoKind
getKindDecl decl = do
  let polyknd = TST.data_kind decl
  return (CBox (returnKind polyknd))

newKVar :: GenM KVar
newKVar = do
  kvCnt <- gets kVarCount
  let kVar = MkKVar (T.pack ("kv" <> show kvCnt))
  modify (\gs@GenerateState{} -> gs { kVarCount = kvCnt + 1 })
  modify (\gs@GenerateState{ constraintSet = cs@ConstraintSet { cs_kvars } } ->
            gs { constraintSet = cs {cs_kvars = cs_kvars ++ [kVar] } })
  return kVar 

--------------------------------------------------------------------------------------------
-- Annotating Data Declarations 
--------------------------------------------------------------------------------------------
-- we can't use the environment here, as the results are inserted into the environment

-- only temporary, will be removed 
defaultKind :: MonoKind
defaultKind = CBox CBV

annotXtor :: PolyKind -> RST.XtorSig pol -> TST.XtorSig pol
annotXtor polyknd (RST.MkXtorSig nm ctxt) = TST.MkXtorSig nm (annotCtxt polyknd ctxt)

annotCtxt :: PolyKind -> RST.LinearContext pol -> TST.LinearContext pol
annotCtxt _ [] = []
annotCtxt polyknd (RST.PrdCnsType pc ty:rst) = TST.PrdCnsType pc (annotTy polyknd ty) : annotCtxt polyknd rst

annotVarTys :: PolyKind -> [RST.VariantType pol] ->[TST.VariantType pol]
annotVarTys _ [] = [] 
annotVarTys polyknd (RST.CovariantType ty:rst) = TST.CovariantType (annotTy polyknd ty) : annotVarTys polyknd rst
annotVarTys polyknd (RST.ContravariantType ty:rst) = TST.ContravariantType (annotTy polyknd ty) : annotVarTys polyknd rst



--data PolyKind =
--  MkPolyKind { kindArgs :: [(Variance, SkolemTVar, MonoKind)]
--             , returnKind :: EvaluationOrder
--             }
getKindSkolem :: PolyKind -> SkolemTVar -> MonoKind
getKindSkolem polyknd = searchKindArgs (kindArgs polyknd)
  where 
    searchKindArgs :: [(Variance, SkolemTVar, MonoKind)] -> SkolemTVar -> MonoKind
    searchKindArgs [] _ = error "Skolem Variable not found in argument types of polykind"
    searchKindArgs ((_,tv,mk):rst) tv' = if tv == tv' then mk else searchKindArgs rst tv'

annotTy :: PolyKind -> RST.Typ pol -> TST.Typ pol
annotTy polyknd (RST.TySkolemVar loc pol tv) = TST.TySkolemVar loc pol (getKindSkolem polyknd tv) tv 
-- uni vars should not appear in data declarations
annotTy _ RST.TyUniVar{} = error "UniVar should not appear in data declaration"
annotTy polyknd (RST.TyRecVar loc pol tv) = TST.TyRecVar loc pol defaultKind tv
annotTy polyknd (RST.TyData loc pol xtors) =  TST.TyData loc pol defaultKind (map (annotXtor polyknd) xtors)
annotTy polyknd (RST.TyCodata loc pol xtors) = TST.TyCodata loc pol defaultKind (map (annotXtor polyknd) xtors)
annotTy polyknd (RST.TyDataRefined loc pol tyn xtors) =  TST.TyDataRefined loc pol defaultKind tyn (map (annotXtor polyknd) xtors)
annotTy polyknd (RST.TyCodataRefined loc pol tyn xtors) = TST.TyCodataRefined loc pol defaultKind tyn  (map (annotXtor polyknd) xtors)
annotTy polyknd (RST.TyNominal loc pol tyn vartys) = TST.TyNominal loc pol defaultKind tyn (annotVarTys polyknd vartys)
annotTy polyknd (RST.TySyn loc pol tyn ty) =  TST.TySyn loc pol tyn (annotTy polyknd ty)
annotTy polyknd (RST.TyBot loc) = TST.TyBot loc defaultKind
annotTy polyknd (RST.TyTop loc) = TST.TyTop loc defaultKind
annotTy polyknd (RST.TyUnion loc ty1 ty2) = TST.TyUnion loc defaultKind (annotTy polyknd ty1) (annotTy polyknd ty2)
annotTy polyknd (RST.TyInter loc ty1 ty2) = TST.TyInter loc defaultKind (annotTy polyknd ty1) (annotTy polyknd ty2)
annotTy polyknd (RST.TyRec loc pol tv ty) = TST.TyRec loc pol tv (annotTy polyknd ty)
annotTy polyknd (RST.TyI64 loc pol) = TST.TyI64 loc pol
annotTy polyknd (RST.TyF64 loc pol) = TST.TyF64 loc pol
annotTy polyknd (RST.TyChar loc pol) = TST.TyChar loc pol
annotTy polyknd (RST.TyString loc pol) = TST.TyString loc pol
annotTy polyknd (RST.TyFlipPol pol ty) = TST.TyFlipPol pol (annotTy polyknd ty)


annotateDataDecl :: RST.DataDecl -> TST.DataDecl 
annotateDataDecl RST.NominalDecl {
  data_loc = loc, 
  data_doc = doc,
  data_name = tyn,
  data_polarity = pol,
  data_kind = polyknd,
  data_xtors = xtors 
  } = 
    TST.NominalDecl { 
        data_loc = loc, 
        data_doc = doc,
        data_name = tyn,
        data_polarity = pol,
        data_kind = polyknd,
        data_xtors = Data.Bifunctor.bimap (map (annotXtor polyknd)) (map (annotXtor polyknd)) xtors
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
  } = 
    TST.RefinementDecl {
      data_loc = loc,
      data_doc = doc,
      data_name = tyn,
      data_polarity = pol ,
      data_refinement_empty = Data.Bifunctor.bimap (annotTy polyknd) (annotTy polyknd) empt,
      data_refinement_full = Data.Bifunctor.bimap (annotTy polyknd) (annotTy polyknd) ful, 
      data_kind = polyknd,
      data_xtors = Data.Bifunctor.bimap (map (annotXtor polyknd)) (map (annotXtor polyknd)) xtors,
      data_xtors_refined = Data.Bifunctor.bimap (map (annotXtor polyknd)) (map (annotXtor polyknd)) xtorsref
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


