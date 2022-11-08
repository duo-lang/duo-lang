module TypeInference.GenerateConstraints.Kinds
  ( AnnotateKind(..)
  , getKindDecl
  , resolveDataDecl
  ) where


import Syntax.TST.Program qualified as TST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.TST.Types qualified as TST
import Syntax.TST.Types (getKind)
import Syntax.CST.Kinds
import Syntax.CST.Names 
import Pretty.Pretty
import Pretty.Types()
import Lookup
import Errors
import Loc
import TypeInference.Constraints
import TypeInference.GenerateConstraints.Definition
import Driver.Environment

import Control.Monad.Reader
import Control.Monad.Except
import Data.List.NonEmpty (NonEmpty(..))
import Control.Monad.State
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Bifunctor (bimap)
import qualified Syntax.CST.Types as CST
import Syntax.RST.Types (Polarity(..), PolarityRep (..))


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
  getKindDecl decl
  
getKindDecl ::  TST.DataDecl -> GenM (MonoKind,[MonoKind])
getKindDecl decl = do
  let polyknd = TST.data_kind decl
  let argKnds = map (\(_,_,mk) -> mk) (kindArgs polyknd)
  return (CBox $ returnKind polyknd, argKnds)

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

data DataDeclState = MkDataDeclState
  {
    declKind :: PolyKind,
    declTyName :: RnTypeName,
    boundRecVars :: M.Map RecTVar MonoKind,
    refXtors :: ([TST.XtorSig RST.Pos], [TST.XtorSig RST.Neg]),
    refRecVars :: M.Map RecTVar MonoKind
  }

createDataDeclState :: PolyKind -> RnTypeName -> DataDeclState
createDataDeclState polyknd tyn = MkDataDeclState 
  { declKind = polyknd,
    declTyName = tyn,
    boundRecVars = M.empty, 
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
annotXtor (RST.MkXtorSig nm ctxt) = do 
  ctxt' <- annotCtxt ctxt
  return $ TST.MkXtorSig nm ctxt'

annotCtxt :: RST.LinearContext pol -> DataDeclM (TST.LinearContext pol)
annotCtxt [] = return []
annotCtxt (RST.PrdCnsType pc ty:rst) = do 
  rst' <- annotCtxt rst
  ty' <- annotTy ty
  return $ TST.PrdCnsType pc ty' : rst'

annotVarTys :: [RST.VariantType pol] -> DataDeclM [TST.VariantType pol]
annotVarTys [] = return [] 
annotVarTys (RST.CovariantType ty:rst) = do
  rst' <- annotVarTys rst 
  ty' <- annotTy ty
  return $ TST.CovariantType ty' : rst'
annotVarTys (RST.ContravariantType ty:rst) = do 
  rst'<- annotVarTys rst 
  ty' <- annotTy ty 
  return $ TST.ContravariantType ty' : rst'


getKindSkolem :: PolyKind -> SkolemTVar -> MonoKind
getKindSkolem polyknd = searchKindArgs (kindArgs polyknd)
  where 
    searchKindArgs :: [(Variance, SkolemTVar, MonoKind)] -> SkolemTVar -> MonoKind
    searchKindArgs [] _ = error "Skolem Variable not found in argument types of polykind"
    searchKindArgs ((_,tv,mk):rst) tv' = if tv == tv' then mk else searchKindArgs rst tv'

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
  let allEq = compXtorKinds (map fst xtorKinds)
  case allEq of 
    Nothing -> throwOtherError loc ["Not all xtors have the same return kind"]
    Just mk -> do 
      xtors' <- mapM annotXtor xtors
      return $ TST.TyData loc pol mk xtors' 
  where
    compXtorKinds :: [MonoKind] -> Maybe MonoKind
    compXtorKinds [] = Nothing 
    compXtorKinds [mk] = Just mk
    compXtorKinds (xtor1:xtor2:rst) = if xtor1==xtor2 then compXtorKinds (xtor2:rst) else Nothing
annotTy (RST.TyCodata loc pol xtors) = do 
  let xtnms = map RST.sig_name xtors
  xtorKinds <- mapM lookupXtorKind xtnms
  let allEq = compXtorKinds (map fst xtorKinds)
  case allEq of 
    Nothing -> throwOtherError loc ["Not all xtors have the same return kind"]
    Just mk -> do 
      xtors' <- mapM annotXtor xtors
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
    let xtors' = (case pol of RST.PosRep -> fst; RST.NegRep -> snd) $ TST.data_xtors decl
    return $ TST.TyDataRefined loc pol (CBox $ returnKind $ TST.data_kind decl) tyn xtors' 
annotTy (RST.TyCodataRefined loc pol tyn xtors) = do 
  tyn' <- gets declTyName
  if tyn == tyn' then do 
    let xtorNames = map RST.sig_name xtors
    xtors' <- getXtors (RST.flipPolarityRep pol) xtorNames
    polyknd <- gets declKind
    return $ TST.TyCodataRefined loc pol (CBox $ returnKind polyknd) tyn xtors'
  else do
    decl <- lookupTypeName loc tyn
    let xtors' = (case pol of RST.PosRep -> snd; RST.NegRep -> fst) $ TST.data_xtors decl
    return $ TST.TyCodataRefined loc pol (CBox $ returnKind (TST.data_kind decl)) tyn xtors'
annotTy (RST.TyNominal loc pol tyn vartys) = do 
  tyn' <- gets declTyName
  vartys' <- annotVarTys vartys
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
  data_xtors = xtors 
  } =do 
    xtorsPos <- mapM annotXtor (fst xtors)
    xtorsNeg <- mapM annotXtor (snd xtors)
    return TST.NominalDecl { 
        data_loc = loc, 
        data_doc = doc,
        data_name = tyn,
        data_polarity = pol,
        data_kind = polyknd,
        data_xtors = (xtorsPos, xtorsNeg) 
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

instance AnnotateKind (Maybe (RST.TypeScheme pol)) (Maybe (TST.TypeScheme pol)) where 
  annotateKind Nothing = return Nothing
  annotateKind (Just ty) = do 
   ty' <- annotateKind ty 
   return (Just ty')

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
    newTVars <- mapM addTVar tvs
    return TST.TypeScheme {ts_loc = loc, ts_vars = newTVars,ts_monotype = ty'}
    where 
      addTVar :: MaybeKindedSkolem -> GenM KindedSkolem
      addTVar (sk, mmk) = do 
        skMap <- gets usedSkolemVars
        case M.lookup sk skMap of 
          Nothing -> throwOtherError defaultLoc ["Skolem Variable " <> ppPrint sk <> " is defined but not used"]
          Just mk -> 
            case mmk of 
              Nothing -> return (sk,mk)
              Just mk' -> do
                addConstraint $ KindEq KindConstraint mk mk' 
                return (sk, mk')
                
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
    xtors' <- mapM annotateKind xtors
    let xtorNames = map TST.sig_name xtors'
    xtorKnds <- mapM lookupXtorKind xtorNames
    compXtorKinds loc xtors' xtorKnds
    knd <- getXtorKinds loc xtors'
    return (TST.TyData loc pol knd xtors')
    where 
      compXtorKinds :: Loc -> [TST.XtorSig pol] -> [(MonoKind,[MonoKind])] -> GenM ()
      compXtorKinds _ [] [] = return ()
      compXtorKinds _ [] (_:_) = error "too many xtor kinds (should not happen)"
      compXtorKinds _ (_:_) [] = error "not all xtor kinds found (should already fail during lookup)"
      compXtorKinds loc (fstXtor:rstXtors) ((mk,_):rstKinds) = do
        let argKnds = map getKind (TST.sig_args fstXtor)
        allEq <- mapM (compMonoKind mk) argKnds
        if and allEq then 
          compXtorKinds loc rstXtors rstKinds 
        else 
          throwOtherError loc ["Kind of Xtor " <> ppPrint argKnds <> " does not match declaration kind " <> ppPrint mk]
      compMonoKind:: MonoKind -> MonoKind -> GenM Bool
      compMonoKind mk (KindVar kv) = do 
        addConstraint $ KindEq KindConstraint mk (KindVar kv) 
        return True
      compMonoKind mk mk' = return (mk == mk')


  annotateKind (RST.TyCodata loc pol xtors) = do 
    xtors' <- mapM annotateKind xtors
    let xtorNames = map TST.sig_name xtors'
    xtorKnds <- mapM lookupXtorKind xtorNames
    compXtorKinds loc xtors' xtorKnds
    knd <- getXtorKinds loc xtors'
    return (TST.TyCodata loc pol knd xtors')
    where 
      compXtorKinds :: Loc -> [TST.XtorSig (RST.FlipPol pol)] -> [(MonoKind,[MonoKind])] -> GenM ()
      compXtorKinds _ [] [] = return ()
      compXtorKinds _ [] (_:_) = error "too many xtor kinds (should not happen)"
      compXtorKinds _ (_:_) [] = error "not all xtor kinds found (should already fail during lookup)"
      compXtorKinds loc (fstXtor:rstXtors) ((mk,_):rstKinds) = do
        let argKnds = map getKind (TST.sig_args fstXtor)
        allEq <- mapM (compMonoKind mk) argKnds
        if and allEq then 
          compXtorKinds loc rstXtors rstKinds 
        else 
          throwOtherError loc ["Kind of Xtor " <> ppPrint argKnds <> " does not match declaration kind " <> ppPrint mk]
      compMonoKind:: MonoKind -> MonoKind -> GenM Bool
      compMonoKind mk (KindVar kv) = do 
        addConstraint $ KindEq KindConstraint mk (KindVar kv) 
        return True
      compMonoKind mk mk' = return (mk == mk')


  annotateKind (RST.TyDataRefined loc pol tyn xtors) = do 
    xtors' <- mapM annotateKind xtors
    decl <- lookupTypeName loc tyn
    knd <- getTyNameKind loc tyn
    checkXtors loc xtors' decl
    return (TST.TyDataRefined loc pol (fst knd) tyn xtors')
    where 
      checkXtors :: Loc -> [TST.XtorSig pol] -> TST.DataDecl -> GenM ()
      checkXtors _ [] _ = return ()
      checkXtors loc (fst:rst) decl = do
        let retKnd = CBox $ returnKind $ TST.data_kind decl
        let retKnds = map getKind (TST.sig_args fst)
        if all (==retKnd) retKnds then
          checkXtors loc rst decl 
        else 
          throwOtherError loc ["Xtors do not have the correct kinds"]

  annotateKind (RST.TyCodataRefined loc pol tyn xtors) = do
    xtors' <- mapM annotateKind xtors
    decl <- lookupTypeName loc tyn
    knd <- getTyNameKind loc tyn
    checkXtors loc xtors' decl
    return (TST.TyCodataRefined loc pol (fst knd) tyn xtors')
    where 
      checkXtors :: Loc -> [TST.XtorSig (RST.FlipPol pol)] -> TST.DataDecl -> GenM ()
      checkXtors _ [] _ = return ()
      checkXtors loc (fst:rst) decl = do
        let retKnd = CBox $ returnKind $ TST.data_kind decl
        let retKnds = map getKind (TST.sig_args fst)
        if all (==retKnd) retKnds then
          checkXtors loc rst decl 
        else 
          throwOtherError loc ["Xtors do not have the correct kinds"]


  annotateKind (RST.TyNominal loc pol tyn vartys) = do 
    vartys' <- mapM annotateKind vartys
    decl <- lookupTypeName loc tyn
    let argKnds = map (\(_, _, mk) -> mk) (kindArgs $ TST.data_kind decl)
    checkArgKnds loc vartys' argKnds
    knd <- getTyNameKind loc tyn
    return (TST.TyNominal loc pol (fst knd) tyn vartys')
    where
      checkArgKnds :: Loc -> [TST.VariantType pol] -> [MonoKind] -> GenM () 
      checkArgKnds _ [] [] = return () 
      checkArgKnds loc (_:_) [] = throwOtherError loc ["Too many type Arguments"]
      checkArgKnds loc [] (_:_) = throwOtherError loc ["Too few type Arguments"]
      checkArgKnds loc (fstVarty:rstVarty) (fstMk:rstMk) = 
        case TST.getKind fstVarty of 
          (KindVar kv) -> do 
            addConstraint (KindEq KindConstraint (KindVar kv) fstMk)
            checkArgKnds loc rstVarty rstMk 
          mk -> 
            if mk == fstMk then do
              checkArgKnds loc rstVarty rstMk 
            else do 
              throwOtherError loc ["Kind of VariantType: " <> ppPrint fstVarty <> " does not match kind of declaration " <> ppPrint fstMk]

             
  annotateKind (RST.TySyn loc pol tn ty) = do 
    ty' <- annotateKind ty 
    return (TST.TySyn loc pol tn ty')

  annotateKind (RST.TyBot loc) = do 
    TST.TyBot loc . KindVar <$> newKVar

  annotateKind (RST.TyTop loc) = do
    TST.TyTop loc . KindVar <$> newKVar

  annotateKind (RST.TyUnion loc ty1 ty2) = do  
    ty1' <- annotateKind ty1
    ty2' <- annotateKind ty2
    kv <- newKVar 
    addConstraint (KindEq KindConstraint (getKind ty1') (getKind ty2'))
    addConstraint (KindEq KindConstraint (KindVar kv) (getKind ty1'))
    return (TST.TyUnion loc (KindVar kv) ty1' ty2')
    
  annotateKind (RST.TyInter loc ty1 ty2) = do
    ty1' <- annotateKind ty1
    ty2' <- annotateKind ty2
    kv <- newKVar 
    addConstraint (KindEq KindConstraint (getKind ty1') (getKind ty2'))
    addConstraint (KindEq KindConstraint (KindVar kv) (getKind ty1'))
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


