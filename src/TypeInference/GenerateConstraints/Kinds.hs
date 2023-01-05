module TypeInference.GenerateConstraints.Kinds
  ( AnnotateKind(..)
  , getKindDecl
  , resolveDataDecl
  ) where


import Syntax.TST.Program qualified as TST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.TST.Types qualified as TST
import Syntax.TST.Types (getMonoKind,getPolyKind)
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
import Data.List.NonEmpty qualified as NE
import Control.Monad.State
import Data.Map qualified as M
import Data.Text qualified as T
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
  (mk, _) <- lookupXtorKind nm 
  return mk
getXtorKinds loc (xtor:xtors) = do 
  let nm = RST.sig_name xtor 
  (mk, _) <- lookupXtorKind nm
  mk' <- getXtorKinds loc xtors
  -- all constructors of a structural type need to have the same return kind
  addConstraint (MonoKindEq KindConstraint mk mk')
  return mk
  
getKindDecl ::  TST.DataDecl -> GenM (MonoKind,[MonoKind])
getKindDecl decl = do
  -- this can never be a kind var
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
    refRecVars :: M.Map RecTVar PolyKind
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

addRecVar :: RecTVar -> PolyKind -> DataDeclM ()
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

annotVarTy :: RST.VariantType pol -> DataDeclM (TST.VariantType pol)
annotVarTy (RST.CovariantType ty) = do
  ty' <- annotTy ty
  return $ TST.CovariantType ty' 
annotVarTy (RST.ContravariantType ty) = do 
  ty' <- annotTy ty 
  return $ TST.ContravariantType ty'


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
    Just pk -> return $ TST.TyRecVar loc pol pk tv
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
annotTy (RST.TyDataRefined loc pol pknd tyn xtors) =  do 
  tyn' <- gets declTyName
  if tyn == tyn' then do
    let xtorNames = map RST.sig_name xtors
    xtors' <- getXtors pol xtorNames
    return $ TST.TyDataRefined loc pol pknd tyn xtors' 
  else do 
    decl <- lookupTypeName loc tyn
    let xtors' = (case pol of RST.PosRep -> fst; RST.NegRep -> snd) $ TST.data_xtors decl
    return $ TST.TyDataRefined loc pol pknd tyn xtors' 
annotTy (RST.TyCodataRefined loc pol pknd tyn xtors) = do 
  tyn' <- gets declTyName
  if tyn == tyn' then do 
    let xtorNames = map RST.sig_name xtors
    xtors' <- getXtors (RST.flipPolarityRep pol) xtorNames
    return $ TST.TyCodataRefined loc pol pknd tyn xtors'
  else do
    decl <- lookupTypeName loc tyn
    let xtors' = (case pol of RST.PosRep -> snd; RST.NegRep -> fst) $ TST.data_xtors decl
    return $ TST.TyCodataRefined loc pol pknd tyn xtors'
annotTy (RST.TyApp loc pol ty args) = do 
  ty' <- annotTy ty 
  args' <- mapM annotVarTy args
  return $ TST.TyApp loc pol ty' args'
annotTy (RST.TyNominal loc pol polyknd tyn) = return $ TST.TyNominal loc pol polyknd tyn
annotTy (RST.TySyn loc pol tyn ty) =  do 
  ty' <- annotTy ty
  return $ TST.TySyn loc pol tyn ty'
annotTy (RST.TyBot loc) = throwOtherError loc ["TyBot should not be contained in a data declaration"]
annotTy (RST.TyTop loc) = throwOtherError loc ["TyTop should not be contained in a data declaration"]
annotTy (RST.TyUnion loc ty1 ty2) = do 
  ty1' <- annotTy ty1 
  ty2' <- annotTy ty2
  let pknd = TST.getPolyKind ty1' 
  if pknd == TST.getPolyKind ty2' then
    case pknd of 
      Nothing -> throwOtherError loc [T.pack ("No polykind for " <> show ty1' <> " in union")]
      Just pk -> return $ TST.TyUnion loc pk ty1' ty2'
  else 
    throwOtherError loc ["Kinds of " <> T.pack ( show ty1' ) <> " and " <> T.pack ( show ty2' ) <> " in union do not match"]

annotTy (RST.TyInter loc ty1 ty2) = do 
  ty1' <- annotTy ty1 
  ty2' <- annotTy ty2
  let pknd = TST.getPolyKind ty1' 
  if pknd == TST.getPolyKind ty2' then 
    case pknd of 
      Nothing -> throwOtherError loc [T.pack ("No polykind for " <> show ty1' <> " in union")]
      Just pk -> return $ TST.TyInter loc pk ty1' ty2'
  else 
    throwOtherError loc ["Kinds of " <> T.pack ( show ty1' ) <> " and " <> T.pack ( show ty2' ) <> " in intersection do not match"]
annotTy (RST.TyRec loc pol rv ty) = case ty of 
  -- recursive types can only appear inside Refinement declarations
  -- when they do, the recvars always represent the type that is being refined
  RST.TyDataRefined loc' pol' pknd tyn xtors -> do 
    addRecVar rv pknd
    xtors' <- mapM annotXtor xtors
    return $ TST.TyRec loc pol rv (TST.TyDataRefined loc' pol' pknd tyn xtors')
  RST.TyCodataRefined loc' pol' pknd tyn xtors -> do
    addRecVar rv pknd
    xtors' <- mapM annotXtor xtors
    return $ TST.TyRec loc pol rv (TST.TyCodataRefined loc' pol' pknd tyn xtors')
  _ -> throwOtherError loc ["TyRec can only appear inside Refinement Declaration"]
annotTy (RST.TyI64 loc pol) = return $ TST.TyI64 loc pol
annotTy (RST.TyF64 loc pol) = return $ TST.TyF64 loc pol
annotTy (RST.TyChar loc pol) = return $ TST.TyChar loc pol
annotTy (RST.TyString loc pol) = return $ TST.TyString loc pol
annotTy (RST.TyFlipPol pol ty) = do 
  ty' <- annotTy ty 
  return $ TST.TyFlipPol pol ty'
annotTy (RST.TyKindAnnot mk ty) = do
  ty' <- annotTy ty
  let knd = getMonoKind ty'
  if knd == mk then
    return ty' 
  else 
    throwOtherError defaultLoc ["Annotated Kind " <> ppPrint mk <> " and Inferred Kind " <> ppPrint knd <> " do not match"]

  


-- | Given the polarity (data/codata) and the name of a type, compute the empty refinement of that type.
-- Example:
--
--   computeEmptyRefinementType Data   Nat = < Nat | >
--   computeEmptyRefinementType Codata Foo = { Foo | }
-- 
computeEmptyRefinementType :: CST.DataCodata
                           -> RnTypeName
                           -> PolyKind
                           -> DataDeclM (RST.Typ Pos, RST.Typ Neg)
computeEmptyRefinementType CST.Data tn polyknd = do 
  pure (RST.TyDataRefined   defaultLoc PosRep polyknd tn [], RST.TyDataRefined   defaultLoc NegRep polyknd tn [])
computeEmptyRefinementType CST.Codata tn polyknd = do 
  pure (RST.TyCodataRefined defaultLoc PosRep polyknd tn [], RST.TyCodataRefined defaultLoc NegRep polyknd tn [])

-- | Given the polarity (data/codata), the name and the constructors/destructors of a type, compute the
-- full refinement of that type.
-- Example:
--
--   computeFullRefinementType Data Nat [Z,S(Nat)] = mu a. < Nat | Z, S(a) >
--
computeFullRefinementType :: CST.DataCodata
                          -> RnTypeName
                          -> ([RST.XtorSig Pos], [RST.XtorSig Neg])
                          -> PolyKind
                          -> DataDeclM (RST.Typ Pos, RST.Typ Neg)
computeFullRefinementType dc tn (xtorsPos, xtorsNeg) polyknd = do
  -- Define the variable that stands for the recursive occurrences in the translation.
  let recVar = MkRecTVar "α"
  let recVarPos = RST.TyRecVar defaultLoc PosRep recVar
  let recVarNeg = RST.TyRecVar defaultLoc NegRep recVar
  -- Replace all the recursive occurrences of the type by the variable "α" in the constructors/destructors.
  let xtorsReplacedPos :: [RST.XtorSig Pos] = RST.replaceNominal recVarPos recVarNeg tn <$> xtorsPos
  let xtorsReplacedNeg :: [RST.XtorSig Neg] = RST.replaceNominal recVarPos recVarNeg tn <$> xtorsNeg
  -- Assemble the 
  let fullRefinementTypePos :: RST.Typ Pos = case dc of
                   CST.Data   -> RST.TyRec defaultLoc PosRep recVar (RST.TyDataRefined   defaultLoc PosRep polyknd tn xtorsReplacedPos)
                   CST.Codata -> RST.TyRec defaultLoc PosRep recVar (RST.TyCodataRefined defaultLoc PosRep polyknd tn xtorsReplacedNeg)
  let fullRefinementTypeNeg :: RST.Typ Neg = case dc of
                   CST.Data   -> RST.TyRec defaultLoc NegRep recVar (RST.TyDataRefined defaultLoc NegRep polyknd tn   xtorsReplacedNeg)
                   CST.Codata -> RST.TyRec defaultLoc NegRep recVar (RST.TyCodataRefined defaultLoc NegRep polyknd tn xtorsReplacedPos)
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
    (emptyPos, emptyNeg) <- computeEmptyRefinementType pol tyn polyknd
    emptPos' <- annotTy emptyPos
    emptNeg' <- annotTy emptyNeg
    (fulPos, fulNeg) <- computeFullRefinementType pol tyn xtors polyknd
    fulPos' <- annotTy fulPos
    fulNeg' <- annotTy fulNeg
    -- Compute the annotated xtors (without refinement)
    xtorsPos <- mapM annotXtor (fst xtors)
    xtorsNeg <- mapM annotXtor (snd xtors)
    addXtors (xtorsPos,xtorsNeg)
    -- Compute the refined xtors:
    let xtorsRefinedPos = RST.replaceNominal emptyPos emptyNeg tyn <$> fst xtors
    -- The negative ones are called by `getXtorSigsUpper` which are used as upper bounds to Xtors!
    let xtorsRefinedNeg = RST.replaceNominal fulPos fulNeg tyn <$> snd xtors
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
    newTVars <- mapM addTVar tvs
    ty' <- annotateKind ty
    return TST.TypeScheme {ts_loc = loc, ts_vars = newTVars,ts_monotype = ty'}
    where 
      addTVar :: MaybeKindedSkolem -> GenM KindedSkolem
      addTVar (sk, mmk) = do 
        skMap <- gets usedSkolemVars
        case (M.lookup sk skMap, mmk) of 
          (Nothing, Nothing) -> do
            kvNew <- newKVar
            let newSkMap = M.insert sk (MKindVar kvNew) skMap
            modify (\gs@GenerateState{} -> gs { usedSkolemVars = newSkMap })
            return (sk,MKindVar kvNew)
          (Just mk,Nothing) -> return (sk,mk)
          (Nothing, Just mk) -> do
            let newSkMap = M.insert sk mk skMap
            modify (\gs@GenerateState{} -> gs { usedSkolemVars = newSkMap })
            return (sk,mk)
          (Just mk, Just mk') -> do
            addConstraint $ MonoKindEq KindConstraint mk mk' 
            return (sk,mk)
                
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
        let newM = M.insert tv (MKindVar kv) skMap
        modify (\gs@GenerateState{} -> gs { usedSkolemVars = newM })
        return (TST.TySkolemVar loc pol (MKindVar kv) tv)
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
      Nothing -> error "Recvar has to be contained in a nominal or structural (refinement) type"
      Just pk -> return (TST.TyRecVar loc pol pk rv)

  annotateKind (RST.TyData loc pol xtors) = do 
    let xtorNames = map RST.sig_name xtors
    xtorKnds <- mapM lookupXtorKind xtorNames
    knd <- getXtorKinds loc xtors
    xtors' <- mapM annotateKind xtors
    compXtorKinds loc xtors' xtorKnds
    return (TST.TyData loc pol knd xtors')
    where 
      compXtorKinds :: Loc -> [TST.XtorSig pol] -> [(MonoKind,[MonoKind])] -> GenM ()
      compXtorKinds _ [] [] = return ()
      compXtorKinds _ [] (_:_) = error "too many xtor kinds (should not happen)"
      compXtorKinds _ (_:_) [] = error "not all xtor kinds found (should already fail during lookup)"
      compXtorKinds loc (fstXtor:rstXtors) ((mk,_):rstKinds) = do
        let argKnds = map getMonoKind (TST.sig_args fstXtor)
        allEq <- mapM (compMonoKind mk) argKnds
        if and allEq then 
          compXtorKinds loc rstXtors rstKinds 
        else 
          throwOtherError loc ["Kind of Xtor " <> ppPrint argKnds <> " does not match declaration kind " <> ppPrint mk]
      compMonoKind:: MonoKind -> MonoKind -> GenM Bool
      compMonoKind mk (MKindVar kv) = do 
        addConstraint $ MonoKindEq KindConstraint mk (MKindVar kv) 
        return True
      compMonoKind mk mk' = return (mk == mk')


  annotateKind (RST.TyCodata loc pol xtors) = do 
    let xtorNames = map RST.sig_name xtors
    xtorKnds <- mapM lookupXtorKind xtorNames
    knd <- getXtorKinds loc xtors
    xtors' <- mapM annotateKind xtors
    compXtorKinds loc xtors' xtorKnds
    return (TST.TyCodata loc pol knd xtors')
    where 
      compXtorKinds :: Loc -> [TST.XtorSig (RST.FlipPol pol)] -> [(MonoKind,[MonoKind])] -> GenM ()
      compXtorKinds _ [] [] = return ()
      compXtorKinds _ [] (_:_) = error "too many xtor kinds (should not happen)"
      compXtorKinds _ (_:_) [] = error "not all xtor kinds found (should already fail during lookup)"
      compXtorKinds loc (fstXtor:rstXtors) ((mk,_):rstKinds) = do
        let argKnds = map getMonoKind (TST.sig_args fstXtor)
        allEq <- mapM (compMonoKind mk) argKnds
        if and allEq then 
          compXtorKinds loc rstXtors rstKinds 
        else 
          throwOtherError loc ["Kind of Xtor " <> ppPrint argKnds <> " does not match declaration kind " <> ppPrint mk]
      compMonoKind:: MonoKind -> MonoKind -> GenM Bool
      compMonoKind mk (MKindVar kv) = do 
        addConstraint $ MonoKindEq KindConstraint mk (MKindVar kv) 
        return True
      compMonoKind mk mk' = return (mk == mk')


  annotateKind (RST.TyDataRefined loc pol pknd tyn xtors) = do 
    xtors' <- mapM annotateKind xtors
    decl <- lookupTypeName loc tyn
    checkXtors loc xtors' decl
    return (TST.TyDataRefined loc pol pknd tyn xtors')
    where 
      checkXtors :: Loc -> [TST.XtorSig pol] -> TST.DataDecl -> GenM ()
      checkXtors _ [] _ = return ()
      checkXtors loc (fst:rst) decl = do
        -- this can never be a kind var
        let retKnd = CBox $ returnKind $ TST.data_kind decl
        let retKnds = map getMonoKind (TST.sig_args fst)
        if all (==retKnd) retKnds then
          checkXtors loc rst decl 
        else 
          throwOtherError loc ["Xtors do not have the correct kinds"]

  annotateKind (RST.TyCodataRefined loc pol pknd tyn xtors) = do
    xtors' <- mapM annotateKind xtors
    decl <- lookupTypeName loc tyn
    checkXtors loc xtors' decl
    return (TST.TyCodataRefined loc pol pknd tyn xtors')
    where 
      checkXtors :: Loc -> [TST.XtorSig (RST.FlipPol pol)] -> TST.DataDecl -> GenM ()
      checkXtors _ [] _ = return ()
      checkXtors loc (fst:rst) decl = do
        -- this can never be a kind  var 
        let retKnd = CBox $ returnKind $ TST.data_kind decl
        let retKnds = map getMonoKind (TST.sig_args fst)
        if all (==retKnd) retKnds then
          checkXtors loc rst decl 
        else 
          throwOtherError loc ["Xtors do not have the correct kinds"]

  annotateKind (RST.TyApp _loc' _pol' (RST.TyNominal loc pol polyknd tyn) vartys) = do 
    vartys' <- mapM annotateKind vartys
    let argKnds = map (\(_, _, mk) -> mk) (kindArgs polyknd)
    if length vartys' /= length argKnds then
      throwOtherError loc ["Wrong number of arguments of type " <> ppPrint tyn] 
    else do
      let argKnds' = case argKnds of (fst:rst) -> fst:|rst; _ -> error "cannnot happen"
      vartys'' <- mapM (checkArgKnds loc) (NE.zip vartys' argKnds')
      return (TST.TyApp loc pol (TST.TyNominal loc pol polyknd tyn) vartys'')
    where
      checkArgKnds :: Loc -> (TST.VariantType pol, MonoKind) -> GenM (TST.VariantType pol)
      checkArgKnds loc (_,MKindVar _) = throwOtherError loc ["Kind variables should not appear in nominal declarations"]
      checkArgKnds loc (varty,mk) =  
        case TST.getMonoKind varty of 
          (MKindVar kv) -> do
            addConstraint (MonoKindEq KindConstraint (MKindVar kv) mk)
            return varty
          mk' -> 
            if mk == mk' then 
              return varty 
            else 
              throwOtherError loc ["Kind of applied type " <> ppPrint varty <> " does not match with declaration"]

  annotateKind (RST.TyNominal loc pol polyknd tyn) = do 
    case kindArgs polyknd of 
      [] -> do 
        return $ TST.TyNominal loc pol polyknd tyn
      _ -> throwOtherError loc ["Nominal Type " <> ppPrint tyn <> " was not fully applied"]
  annotateKind (RST.TyApp loc _ ty _ ) = throwOtherError loc ["Types can only be applied to nominal types, was applied to ", ppPrint ty]
             
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
    addConstraint (MonoKindEq KindConstraint (getMonoKind ty1') (getMonoKind ty2'))
    let pk = getPolyKind ty1'
    case pk of 
      Just pk' -> do 
        addConstraint (KindEq KindConstraint (KindVar kv) pk')
        return (TST.TyUnion loc (KindVar kv) ty1' ty2')
      _ -> return (TST.TyUnion loc (KindVar kv) ty1' ty2')
    
  annotateKind (RST.TyInter loc ty1 ty2) = do
    ty1' <- annotateKind ty1
    ty2' <- annotateKind ty2
    kv <- newKVar 
    addConstraint (MonoKindEq KindConstraint (getMonoKind ty1') (getMonoKind ty2'))
    let pk = getPolyKind ty1'
    case pk of 
      Just pk' -> do 
        addConstraint (KindEq KindConstraint (KindVar kv) pk')
        return (TST.TyInter loc (KindVar kv) ty1' ty2')
      _ -> return (TST.TyInter loc (KindVar kv) ty1' ty2') 
    
  annotateKind (RST.TyRec loc pol rv ty) = do
    pknd <- getPk ty
    insertPk rv pknd
    ty' <- annotateKind ty
    return (TST.TyRec loc pol rv ty')
      where 
        getPk :: RST.Typ pol -> GenM PolyKind
        getPk (RST.TyData loc _ xtors) = do
          retK <- getXtorKinds loc xtors
          case retK of 
            CBox eo -> return (MkPolyKind [] eo)
            _ -> throwOtherError defaultLoc ["Structural Type can only have CBV or CBN as kind"]
        getPk (RST.TyCodata loc _ xtors) = do
          retK <- getXtorKinds loc xtors
          case retK of 
            CBox eo -> return (MkPolyKind [] eo)
            _ -> throwOtherError defaultLoc ["Structural Type can only have CBV or CBN as kind"]
        getPk (RST.TyNominal _ _ pk _) = return pk
        getPk (RST.TyDataRefined _ _ pknd _ _) = return pknd
        getPk (RST.TyCodataRefined _ _ pknd _ _) = return pknd
        getPk (RST.TyKindAnnot _ ty) = getPk ty
        getPk _ = throwOtherError defaultLoc ["could not find polykind (not fully implemented)"]

        insertPk :: RecTVar -> PolyKind -> GenM ()
        insertPk rv knd = do  
          rvMap <- gets usedRecVars
          let newM = M.insert rv knd rvMap
          modify (\gs@GenerateState{} -> gs { usedRecVars = newM })

  annotateKind (RST.TyI64 loc pol) = return (TST.TyI64 loc pol)
  annotateKind (RST.TyF64 loc pol) = return (TST.TyF64 loc pol)
  annotateKind (RST.TyChar loc pol) = return (TST.TyChar loc pol)
  annotateKind (RST.TyString loc pol) = return(TST.TyString loc pol)

  annotateKind (RST.TyFlipPol pol ty) = do 
    ty' <- annotateKind ty
    return (TST.TyFlipPol pol ty')
  
  annotateKind (RST.TyKindAnnot mk ty) = do 
    ty' <- annotateKind ty 
    addConstraint $ MonoKindEq KindConstraint (TST.getMonoKind ty') mk 
    return ty'



