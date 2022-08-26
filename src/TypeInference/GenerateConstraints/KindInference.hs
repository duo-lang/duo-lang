module TypeInference.GenerateConstraints.KindInference where

import Syntax.RST.Types qualified as RST
import Syntax.RST.Types (Polarity(..))
import Syntax.TST.Types qualified as TST
import Syntax.TST.Types (getKind)
import Syntax.CST.Kinds
import Syntax.CST.Names 
import Lookup
import Errors
import Driver.Environment

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State
import Data.List.NonEmpty
import Data.Map 

--------------------------------------------------------------------------------------------
-- Kind Inference Monad 
--------------------------------------------------------------------------------------------
--type KindedTypes = (S.Set (TST.Typ Pos), S.Set (TST.Typ Neg))

data KindState = KindState { posTypes :: [TST.Typ Pos], negTypes :: [TST.Typ Neg] } 
initialState :: KindState
initialState = KindState { posTypes = [], negTypes = []}

-- newtype KindReader = KindReader {location :: Loc}
--initialReader:: Loc -> Map ModuleName Environment -> (Map ModuleName Environment,KindReader)
-- initialReader loc env = (env, KindReader {location = loc})

type KindM a = (ReaderT (Map ModuleName Environment, ()) (StateT KindState (Except (NonEmpty Error)))) a
 

runKindM ::  KindM a -> Map ModuleName Environment -> KindState -> Either (NonEmpty Error) (a, KindState)
runKindM m env initSt = runExcept (runStateT (runReaderT m (env,())) initSt)
--------------------------------------------------------------------------------------------
-- Kind Inference
--------------------------------------------------------------------------------------------
getXtorKinds :: [RST.XtorSig pol] -> KindM (Maybe MonoKind)
getXtorKinds [] = return Nothing
getXtorKinds (fst:rst) = do
  let nm = RST.sig_name fst
  knd <- Just <$> lookupXtorKind nm
  knd' <- getXtorKinds rst
  if knd == knd' then return knd else error "Kinds of constructors do not match" 


checkTypeScheme :: RST.TypeScheme pol -> KindM (TST.TypeScheme pol)
checkTypeScheme RST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty} = do
  ty' <- checkKind ty
  return TST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty'}

checkVariantType :: RST.VariantType pol -> KindM (TST.VariantType pol)
checkVariantType (RST.CovariantType ty) = TST.CovariantType <$> checkKind ty
checkVariantType (RST.ContravariantType ty) = TST.ContravariantType <$> checkKind ty

checkPrdCnsType :: RST.PrdCnsType pol -> KindM (TST.PrdCnsType pol)
checkPrdCnsType (RST.PrdCnsType rep ty) = do 
  ty' <- checkKind ty
  return (TST.PrdCnsType rep ty')

checkLinearContext :: RST.LinearContext pol -> KindM (TST.LinearContext pol)
checkLinearContext = mapM checkPrdCnsType

checkXtorSig :: RST.XtorSig pol -> KindM (TST.XtorSig pol)
checkXtorSig RST.MkXtorSig { sig_name = nm, sig_args = ctxt } = do 
  ctxt' <- checkLinearContext ctxt 
  return (TST.MkXtorSig {sig_name = nm, sig_args = ctxt' })

checkKind :: RST.Typ pol -> KindM (TST.Typ pol)
checkKind (RST.TySkolemVar loc pol tv) = do
  let knd = KindVar (MkKVar (unSkolemTVar tv))
  return (TST.TySkolemVar loc pol (Just knd) tv)

checkKind (RST.TyUniVar loc pol tv) = do 
  let knd = KindVar (MkKVar (unUniTVar tv))
  return (TST.TyUniVar loc pol (Just knd) tv)

checkKind (RST.TyRecVar loc pol rv) = do
  let knd = KindVar (MkKVar (unRecTVar rv))
  return (TST.TyRecVar loc pol (Just knd) rv)

checkKind (RST.TyData loc pol xtors) = do 
  knd <- getXtorKinds xtors 
  xtors' <- mapM checkXtorSig xtors
  return (TST.TyData loc pol knd xtors')

checkKind (RST.TyCodata loc pol xtors) = do 
  knd <- getXtorKinds xtors
  xtors' <- mapM checkXtorSig xtors
  return (TST.TyCodata loc pol knd xtors')

-- TODO
checkKind (RST.TyDataRefined loc pol tn xtors) = do
  xtors' <- mapM checkXtorSig xtors
  return (TST.TyDataRefined loc pol Nothing tn xtors')
checkKind (RST.TyCodataRefined loc pol tn xtors) = do 
  xtors' <- mapM checkXtorSig xtors
  return (TST.TyCodataRefined loc pol Nothing tn xtors')
checkKind (RST.TyNominal loc pol tn vart) = do
  vart' <- mapM checkVariantType vart
  return (TST.TyNominal loc pol Nothing tn vart')
---

checkKind (RST.TySyn loc pol tn ty) = do 
  ty' <- checkKind ty 
  return (TST.TySyn loc pol tn ty')

checkKind (RST.TyBot loc) = return (TST.TyBot loc (Just topbotVar))
checkKind (RST.TyTop loc) = return (TST.TyTop loc (Just topbotVar))

checkKind (RST.TyUnion loc ty1 ty2) = do 
  ty1' <- checkKind ty1
  ty2' <- checkKind ty2
  let knd = getKind ty1'
  if knd == getKind ty2' then
    return (TST.TyUnion loc knd ty1' ty2')
  else
    error ("Union of types " <> show ty1 <> " and " <> show ty2 <> " with different kinds")

checkKind (RST.TyInter loc ty1 ty2) = do
  ty1' <- checkKind ty1
  ty2' <- checkKind ty2
  let knd = getKind ty1'
  if knd == getKind ty2' then
    return (TST.TyInter loc knd ty1' ty2')
  else
    error ("Intersection of types " <> show ty1 <> " and " <> show ty2 <> " with different kinds")

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


-- insert Type into state
insertType :: TST.Typ pol -> KindM ()
insertType ty = do
  posTy <- gets posTypes
  negTy <- gets negTypes
  case TST.getPolarity ty of 
   RST.PosRep -> modify (\s -> s { posTypes = ty:posTy })
   RST.NegRep ->  modify (\s -> s { negTypes = ty:negTy })

-- check a list of kinds and insert them all into the environment
checkKinds :: [RST.Typ pol] -> KindM ()
checkKinds [] = return ()
checkKinds (ty:tys) = do
  ty' <- checkKind ty
  insertType ty'
  checkKinds tys

---------------------------------------------------------------------------------
-- Run Kind Inference
---------------------------------------------------------------------------------

inferKindsTypes :: ([RST.Typ Pos],[RST.Typ Neg]) -> Map ModuleName Environment -> Either (NonEmpty Error) ([TST.Typ Pos], [TST.Typ Neg])
inferKindsTypes typs env = do 
  (_, posSt) <- runKindM (checkKinds (fst typs)) env initialState
  (_, kindSt) <- runKindM (checkKinds (snd typs)) env posSt
  Right (posTypes kindSt,negTypes kindSt)
