module TypeInference.GenerateConstraints.Kinds
  ( AnnotateKind(..)
  , getKindDecl
  , resolveDataDecl
  ) where

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
import Data.Foldable (find)
import Data.Bifunctor (bimap)
import qualified Syntax.CST.Types as CST
import Syntax.RST.Types (Polarity(..), PolarityRep (..))

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
  pure (getKindDecl decl)
  
getKindDecl ::  TST.DataDecl -> MonoKind
getKindDecl decl = CBox (returnKind (TST.data_kind decl))

newKVar :: GenM KVar
newKVar = do
  kvCnt <- gets kVarCount
  modify (\gs@GenerateState{} -> gs { kVarCount = kvCnt + 1 })
  return (MkKVar (T.pack ("kv" <> show kvCnt)))

--------------------------------------------------------------------------------------------
-- Annotating Data Declarations 
--------------------------------------------------------------------------------------------

data DataDeclState = MkDataDeclState
  {
    declKind :: PolyKind,
    declTyName :: RnTypeName,
    refXtors :: ([TST.XtorSig RST.Pos], [TST.XtorSig RST.Neg]),
    refRecVars :: M.Map RecTVar MonoKind
  }

createDataDeclState :: PolyKind -> RnTypeName -> DataDeclState
createDataDeclState polyknd tyn = MkDataDeclState 
  { declKind = polyknd,
    declTyName = tyn,
    refXtors = ([],[]), 
    refRecVars = M.empty
  }

type DataDeclM a = (ReaderT (M.Map ModuleName Environment, ()) (StateT DataDeclState (Except (NonEmpty Error)))) a

runDataDeclM :: DataDeclM a -> M.Map ModuleName Environment -> DataDeclState -> Either (NonEmpty Error) (a,DataDeclState)
runDataDeclM m env initSt = runExcept (runStateT (runReaderT m (env,())) initSt)

resolveDataDecl :: RST.DataDecl -> M.Map ModuleName Environment ->  Either (NonEmpty Error) TST.DataDecl
resolveDataDecl decl env = do
  (decl', _) <- runDataDeclM (annotateDataDecl decl) env (createDataDeclState (RST.data_kind decl) (RST.data_name decl))
  return decl' 

addXtors :: ([TST.XtorSig RST.Pos],[TST.XtorSig RST.Neg]) -> DataDeclM ()
addXtors newXtors =  modify (\s@MkDataDeclState{refXtors = xtors} -> 
                                s {refXtors = Data.Bifunctor.bimap (fst xtors ++ ) (snd xtors ++) newXtors })

addRecVar :: RecTVar -> MonoKind -> DataDeclM ()
addRecVar rv mk = modify (\s@MkDataDeclState{refRecVars = recVarMap} -> 
                              s {refRecVars = M.insert rv mk recVarMap})

getXtors :: RST.PolarityRep pol -> [XtorName] -> DataDeclM [TST.XtorSig pol]
getXtors pl names = do
  cached <- gets refXtors
  let f = filter (\(x::TST.XtorSig RST.Pos) -> TST.sig_name x `elem` names)
  let g = filter (\(x::TST.XtorSig RST.Neg) -> TST.sig_name x `elem` names)
  case pl of 
    RST.PosRep -> return (f (fst cached))
    RST.NegRep -> return (g (snd cached))
  
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
    searchKindArgs l tv = case find (\(_,tv',_) -> tv == tv') l of
                            Nothing -> error "Skolem Variable not found in argument types of polykind"
                            Just (_,_,mk) -> mk

annotTy :: RST.Typ pol -> DataDeclM (TST.Typ pol)
annotTy (RST.TySkolemVar loc pol tv) = do 
  polyknd <- gets declKind
  return $ TST.TySkolemVar loc pol (getKindSkolem polyknd tv) tv 
-- uni vars should not appear in data declarations
annotTy (RST.TyUniVar loc _ _) = throwOtherError loc ["UniVar should not appear in data declaration"]
annotTy (RST.TyRecVar loc pol tv) = do
  rVarMap <- gets refRecVars
  case M.lookup tv rVarMap of 
    Nothing -> throwOtherError loc ["Unbound RecVar " <> ppPrint tv <> " in data declaration"]
    Just mk -> return $ TST.TyRecVar loc pol mk tv
annotTy (RST.TyData loc pol xtors) = do 
  let xtnms = map RST.sig_name xtors
  xtorKinds <- mapM lookupXtorKind xtnms
  xtors' <- mapM (flip (lookupXtorSig loc) pol) xtnms
  let allEq = compXtorKinds xtorKinds  
  case allEq of 
    Nothing -> throwOtherError loc ["Not all xtors have the same return kind"]
    Just mk -> do 
      return $ TST.TyData loc pol mk xtors'
  where 
    compXtorKinds :: [MonoKind] -> Maybe MonoKind
    compXtorKinds [] = Nothing 
    compXtorKinds [mk] = Just mk
    compXtorKinds (xtor1:xtor2:rst) = if xtor1==xtor2 then compXtorKinds (xtor2:rst) else Nothing
annotTy (RST.TyCodata loc pol xtors) = do 
  let xtnms = map RST.sig_name xtors
  xtorKinds <- mapM lookupXtorKind xtnms
  xtors' <- mapM (flip (lookupXtorSig loc) (RST.flipPolarityRep pol)) xtnms
  let allEq = compXtorKinds xtorKinds  
  case allEq of 
    Nothing -> throwOtherError loc ["Not all xtors have the same return kind"]
    Just mk -> do 
      return $ TST.TyCodata loc pol mk xtors' 
  where 
    compXtorKinds :: [MonoKind] -> Maybe MonoKind
    compXtorKinds [] = Nothing 
    compXtorKinds [mk] = Just mk
    compXtorKinds (xtor1:xtor2:rst) = if xtor1==xtor2 then compXtorKinds (xtor2:rst) else Nothing
annotTy (RST.TyDataRefined loc pol tyn xtors) =  do 
  tyn' <- gets declTyName
  if tyn == tyn' then do
    let xtorNames = map RST.sig_name xtors
    xtors' <- getXtors pol xtorNames 
    polyknd <- gets declKind
    return $ TST.TyDataRefined loc pol (CBox $ returnKind polyknd) tyn xtors' 
  else do 
    decl <- lookupTypeName loc tyn
    let xtors = (case pol of RST.PosRep -> fst; RST.NegRep -> snd) $ TST.data_xtors decl
    return $ TST.TyDataRefined loc pol (CBox $ returnKind $ TST.data_kind decl) tyn xtors
annotTy (RST.TyCodataRefined loc pol tyn xtors) = do  
  tyn' <- gets declTyName
  if tyn == tyn' then do 
    let xtorNames = map RST.sig_name xtors
    xtors' <- getXtors (RST.flipPolarityRep pol) xtorNames 
    polyknd <- gets declKind
    return $ TST.TyCodataRefined loc pol (CBox $ returnKind polyknd) tyn xtors'
  else do
    decl <- lookupTypeName loc tyn
    let xtors = (case pol of RST.PosRep -> snd; RST.NegRep -> fst) $ TST.data_xtors decl
    return $ TST.TyCodataRefined loc pol (CBox $ returnKind (TST.data_kind decl)) tyn xtors
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
annotTy (RST.TyBot loc) = throwOtherError loc ["TyBot should not be contained in a data declaration"]
annotTy (RST.TyTop loc) = throwOtherError loc ["TyTop should not be contained in a data declaration"]
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
annotTy (RST.TyRec loc pol rv ty) = case ty of 
  -- recursive types can only appear inside Refinement declarations
  -- when they do, the recvars always represent the type that is being refined
  RST.TyDataRefined loc' pol' tyn xtors -> do 
    tyn' <- gets declTyName
    if tyn == tyn' then do
     polyknd <- gets declKind
     let retKnd = CBox $ returnKind polyknd
     addRecVar rv retKnd
     xtors' <- mapM annotXtor xtors
     return $ TST.TyRec loc pol rv (TST.TyDataRefined loc' pol' retKnd tyn xtors')
    else do
     decl <- lookupTypeName loc' tyn
     let retKnd = CBox $ returnKind . TST.data_kind $ decl
     addRecVar rv retKnd
     xtors' <- mapM annotXtor xtors
     return $ TST.TyRec loc pol rv (TST.TyDataRefined loc' pol' retKnd tyn xtors')
  RST.TyCodataRefined loc' pol' tyn xtors -> do
    tyn' <- gets declTyName
    if tyn == tyn' then do
     polyknd <- gets declKind
     let retKnd = CBox $ returnKind polyknd
     addRecVar rv retKnd
     xtors' <- mapM annotXtor xtors
     return $ TST.TyRec loc pol rv (TST.TyCodataRefined loc' pol' retKnd tyn xtors')
    else do
     decl <- lookupTypeName loc' tyn
     let retKnd = CBox $ returnKind . TST.data_kind $ decl
     addRecVar rv retKnd
     xtors' <- mapM annotXtor xtors
     return $ TST.TyRec loc pol rv (TST.TyCodataRefined loc' pol' retKnd tyn xtors')
  _ -> throwOtherError loc ["TyRec can only appear inside Refinement Declaration"]
annotTy (RST.TyI64 loc pol) = return $ TST.TyI64 loc pol
annotTy (RST.TyF64 loc pol) = return $ TST.TyF64 loc pol
annotTy (RST.TyChar loc pol) = return $ TST.TyChar loc pol
annotTy (RST.TyString loc pol) = return $ TST.TyString loc pol
annotTy (RST.TyFlipPol pol ty) = do 
  ty' <- annotTy ty 
  return $ TST.TyFlipPol pol ty'


-- | Given the polarity (data/codata) and the name of a type, compute the empty refinement of that type.
-- Example:
--
--   computeEmptyRefinementType Data   Nat = < Nat | >
--   computeEmptyRefinementType Codata Foo = { Foo | }
-- 
computeEmptyRefinementType :: CST.DataCodata
                           -> RnTypeName
                           -> DataDeclM (RST.Typ Pos, RST.Typ Neg)
computeEmptyRefinementType CST.Data   tn =
  pure (RST.TyDataRefined   defaultLoc PosRep tn [], RST.TyDataRefined   defaultLoc NegRep tn [])
computeEmptyRefinementType CST.Codata tn =
  pure (RST.TyCodataRefined defaultLoc PosRep tn [], RST.TyCodataRefined defaultLoc NegRep tn [])

-- | Given the polarity (data/codata), the name and the constructors/destructors of a type, compute the
-- full refinement of that type.
-- Example:
--
--   computeFullRefinementType Data Nat [Z,S(Nat)] = mu a. < Nat | Z, S(a) >
--
computeFullRefinementType :: CST.DataCodata
                          -> RnTypeName
                          -> ([RST.XtorSig Pos], [RST.XtorSig Neg])
                          -> DataDeclM (RST.Typ Pos, RST.Typ Neg)
computeFullRefinementType dc tn (xtorsPos, xtorsNeg) = do
  -- Define the variable that stands for the recursive occurrences in the translation.
  let recVar = MkRecTVar "α"
  let recVarPos = RST.TyRecVar defaultLoc PosRep recVar
  let recVarNeg = RST.TyRecVar defaultLoc NegRep recVar
  -- Replace all the recursive occurrences of the type by the variable "α" in the constructors/destructors.
  let xtorsReplacedPos :: [RST.XtorSig Pos] = RST.replaceNominal recVarPos recVarNeg tn <$> xtorsPos
  let xtorsReplacedNeg :: [RST.XtorSig Neg] = RST.replaceNominal recVarPos recVarNeg tn <$> xtorsNeg
  -- Assemble the 
  let fullRefinementTypePos :: RST.Typ Pos = case dc of
                   CST.Data   -> RST.TyRec defaultLoc PosRep recVar (RST.TyDataRefined   defaultLoc PosRep tn xtorsReplacedPos)
                   CST.Codata -> RST.TyRec defaultLoc PosRep recVar (RST.TyCodataRefined defaultLoc PosRep tn xtorsReplacedNeg)
  let fullRefinementTypeNeg :: RST.Typ Neg = case dc of
                   CST.Data   -> RST.TyRec defaultLoc NegRep recVar (RST.TyDataRefined defaultLoc NegRep tn   xtorsReplacedNeg)
                   CST.Codata -> RST.TyRec defaultLoc NegRep recVar (RST.TyCodataRefined defaultLoc NegRep tn xtorsReplacedPos)
  pure (fullRefinementTypePos, fullRefinementTypeNeg)

annotateDataDecl :: RST.DataDecl -> DataDeclM TST.DataDecl 
annotateDataDecl RST.NominalDecl {
  data_loc = loc, 
  data_doc = doc,
  data_name = tyn,
  data_polarity = pol,
  data_kind = polyknd,
  data_xtors = (xtorsPos, xtorsNeg)
  } = do 
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
  data_kind = polyknd,
  data_xtors = xtors
  } = do
    -- Compute the full and empty refinement types:
    (emptyPos, emptyNeg) <- computeEmptyRefinementType pol tyn
    emptPos' <- annotTy emptyPos
    emptNeg' <- annotTy emptyNeg
    (fulPos, fulNeg) <- computeFullRefinementType pol tyn xtors
    fulPos' <- annotTy fulPos
    fulNeg' <- annotTy fulNeg
    -- Compute the annotated xtors (without refinement)
    xtorsPos <- mapM annotXtor (fst xtors)
    xtorsNeg <- mapM annotXtor (snd xtors)
    addXtors (xtorsPos,xtorsNeg)
    -- Compute the refined xtors:
    let xtorsRefinedPos = RST.replaceNominal emptyPos emptyNeg tyn <$> (fst xtors)
    -- The negative ones are called by `getXtorSigsUpper` which are used as upper bounds to Xtors!
    let xtorsRefinedNeg = RST.replaceNominal fulPos fulNeg tyn <$> (snd xtors)
    xtorsRefPos <- mapM annotXtor xtorsRefinedPos
    xtorsRefNeg <- mapM annotXtor xtorsRefinedNeg
    return TST.RefinementDecl {
      data_loc = loc,
      data_doc = doc,
      data_name = tyn,
      data_polarity = pol ,
      data_refinement_empty = (emptPos', emptNeg'), 
      data_refinement_full = (fulPos', fulNeg'), 
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


