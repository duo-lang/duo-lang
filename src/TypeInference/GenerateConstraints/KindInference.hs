module TypeInference.GenerateConstraints.KindInference where

import Syntax.RST.Types qualified as RST
import Syntax.TST.Types qualified as TST
import Syntax.TST.Types (getKind)
import Syntax.CST.Kinds
import Syntax.CST.Names 
import Lookup
import Errors
import Driver.Environment
import Utils

import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.Writer
import Control.Monad.State
import Data.List.NonEmpty
import Data.Map 

--------------------------------------------------------------------------------------------
-- Kind Inference Monad 
--------------------------------------------------------------------------------------------
newtype KindState = KindState { kVarCount :: Int } 

newtype KindReader = KindReader {location :: Loc}

newtype KindM a = KindM {getKindM :: ReaderT (Map ModuleName Environment, KindReader) (StateT KindState (ExceptT (NonEmpty Error) (Writer [Warning]))) a}
  deriving (Functor, Applicative, Monad, MonadState KindState, MonadReader (Map ModuleName Environment, KindReader), MonadError (NonEmpty Error) )

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
