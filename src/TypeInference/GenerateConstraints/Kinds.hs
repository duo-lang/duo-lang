module TypeInference.GenerateConstraints.Kinds where

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

import Control.Monad.State
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Bifunctor (bimap)


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
  getKindDecl decl
  
getKindDecl ::  TST.DataDecl -> GenM MonoKind
getKindDecl decl = do
  let polyknd = TST.data_kind decl
  return (CBox (returnKind polyknd))

newKVar :: GenM KVar
newKVar = do
  kvCnt <- gets kVarCount
  modify (\gs@GenerateState{} -> gs { kVarCount = kvCnt + 1 })
  return (MkKVar (T.pack ("kv" <> show kvCnt)))

--------------------------------------------------------------------------------------------
-- Annotating Data Declarations 
--------------------------------------------------------------------------------------------
-- we can't use the environment here, as the results are inserted into the environment

-- only temporary, will be removed 
defaultKind :: MonoKind
defaultKind = CBox CBV

annotXtor :: RST.XtorSig pol -> Either Error (TST.XtorSig pol)
annotXtor (RST.MkXtorSig nm ctxt) = 
  case annotCtxt ctxt of 
    Left err -> Left err 
    Right ctxt' -> Right $ TST.MkXtorSig nm ctxt'

annotCtxt :: RST.LinearContext pol -> Either Error (TST.LinearContext pol)
annotCtxt [] = Right []
annotCtxt (RST.PrdCnsType pc ty:rst) = 
  case annotTy ty of
    Left err -> Left err 
    Right ty' -> 
      case annotCtxt rst of 
        Left err -> Left err
        Right ctxt -> Right $ TST.PrdCnsType  pc ty' : ctxt

annotVarTys :: [RST.VariantType pol] -> Either Error [TST.VariantType pol]
annotVarTys [] = Right [] 
annotVarTys (RST.CovariantType ty:rst) = 
  case annotTy ty of 
    Left err -> Left err 
    Right ty' -> 
      case annotVarTys rst of 
        Left err -> Left err 
        Right vartys -> Right $ TST.CovariantType ty' : vartys
annotVarTys (RST.ContravariantType ty:rst) = 
  case annotTy ty of 
    Left err -> Left err 
    Right ty' -> 
      case annotVarTys rst of 
        Left err -> Left err 
        Right vartys -> Right $ TST.ContravariantType ty' : vartys

collectErrs:: [Either Error a] -> Either Error [a]
collectErrs [] = Right []
collectErrs (fst:rst) = case fst of 
  Left err -> Left err 
  Right res -> 
    case collectErrs rst of 
      Left err -> Left err 
      Right res' -> Right $ res:res'


annotTy :: RST.Typ pol -> Either Error (TST.Typ pol)
annotTy (RST.TySkolemVar loc pol tv) = Right $ TST.TySkolemVar loc pol defaultKind tv 
annotTy (RST.TyUniVar loc pol tv) = Right $ TST.TyUniVar loc pol defaultKind tv
annotTy (RST.TyRecVar loc pol tv) = Right $ TST.TyRecVar loc pol defaultKind tv
annotTy (RST.TyData loc pol xtors) = 
  case collectErrs (map annotXtor xtors) of 
    Left err -> Left err 
    Right xtors' -> Right $ TST.TyData loc pol defaultKind xtors'
annotTy (RST.TyCodata loc pol xtors) = 
  case collectErrs (map annotXtor xtors) of 
    Left err -> Left err 
    Right xtors' -> Right $ TST.TyCodata loc pol defaultKind xtors'
annotTy (RST.TyDataRefined loc pol tyn xtors) = 
  case collectErrs (map annotXtor xtors) of 
    Left err -> Left err 
    Right xtors' -> Right $ TST.TyDataRefined loc pol defaultKind tyn xtors'
annotTy (RST.TyCodataRefined loc pol tyn xtors) = 
  case collectErrs (map annotXtor xtors) of 
    Left err -> Left err 
    Right xtors' -> Right $ TST.TyCodataRefined loc pol defaultKind tyn xtors'
annotTy (RST.TyNominal loc pol tyn vartys) = 
  case annotVarTys vartys of 
    Left err -> Left err 
    Right vartys' -> Right $ TST.TyNominal loc pol defaultKind tyn vartys'
annotTy (RST.TySyn loc pol tyn ty) = 
  case annotTy ty of 
    Left err -> Left err 
    Right ty' -> Right $ TST.TySyn loc pol tyn ty'
annotTy (RST.TyBot loc) = Right $ TST.TyBot loc defaultKind
annotTy (RST.TyTop loc) = Right $  TST.TyTop loc defaultKind
annotTy (RST.TyUnion loc ty1 ty2) =
  case annotTy ty1 of 
    Left err -> Left err 
    Right ty1' -> 
      case annotTy ty2 of 
        Left err -> Left err 
        Right ty2' -> Right $ TST.TyUnion loc defaultKind ty1' ty2'
annotTy (RST.TyInter loc ty1 ty2) = 
  case annotTy ty1 of 
    Left err -> Left err 
    Right ty1' -> 
      case annotTy ty2 of 
        Left err -> Left err 
        Right ty2' -> Right $ TST.TyInter loc defaultKind ty1' ty2' 
annotTy (RST.TyRec loc pol tv ty) = 
  case annotTy ty of 
    Left err -> Left err 
    Right ty' -> Right $ TST.TyRec loc pol tv ty'
annotTy (RST.TyI64 loc pol) = Right $ TST.TyI64 loc pol
annotTy (RST.TyF64 loc pol) = Right $ TST.TyF64 loc pol
annotTy (RST.TyChar loc pol) = Right $ TST.TyChar loc pol
annotTy (RST.TyString loc pol) = Right $ TST.TyString loc pol
annotTy (RST.TyFlipPol pol ty) = 
  case annotTy ty of 
    Left err -> Left err 
    Right ty' -> Right $ TST.TyFlipPol pol ty'


annotateDataDecl :: RST.DataDecl -> Either Error TST.DataDecl 
annotateDataDecl RST.NominalDecl {
  data_loc = loc, 
  data_doc = doc,
  data_name = tyn,
  data_polarity = pol,
  data_kind = polyknd,
  data_xtors = xtors 
  } = do
  let xtors' = Data.Bifunctor.bimap (collectErrs . map annotXtor) (collectErrs . map annotXtor) xtors
  case xtors' of 
    (Left err , _) -> Left err
    (_, Left err) -> Left err 
    (Right xtorsPol, Right xtorsNeg)-> 
      Right TST.NominalDecl { 
        data_loc = loc, 
        data_doc = doc,
        data_name = tyn,
        data_polarity = pol,
        data_kind = polyknd,
        data_xtors = (xtorsPol,xtorsNeg)
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
  } =  do
  let empt' = Data.Bifunctor.bimap annotTy annotTy empt
  let ful' = Data.Bifunctor.bimap annotTy annotTy ful
  let xtors' = Data.Bifunctor.bimap (collectErrs . map annotXtor) (collectErrs . map annotXtor) xtors
  let xtorsref' = Data.Bifunctor.bimap (collectErrs . map annotXtor) (collectErrs . map annotXtor) xtorsref
  case empt' of 
    (Left err,_) -> Left err 
    (_, Left err) -> Left err 
    (Right emptPos,Right emptNeg) -> 
      case ful' of 
        (Left err,_)-> Left err 
        (_,Left err) -> Left err 
        (Right fulPos, Right fulNeg) -> 
          case xtors' of 
            (Left err,_) -> Left err 
            (_,Left err) -> Left err
            (Right xtorsPos, Right xtorsNeg) -> 
              case xtorsref' of 
                (Left err,_) -> Left err
                (_,Left err) -> Left err 
                (Right xtorsrefPos, Right xtorsrefNeg) -> 
                  Right TST.RefinementDecl {
                    data_loc = loc,
                    data_doc = doc,
                    data_name = tyn,
                    data_polarity = pol ,
                    data_refinement_empty = (emptPos,emptNeg),
                    data_refinement_full = (fulPos, fulNeg),
                    data_kind = polyknd,
                    data_xtors = (xtorsPos, xtorsNeg),
                    data_xtors_refined = (xtorsrefPos, xtorsrefNeg)
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
annotateLinearContext = mapM annotatePrdCnsType

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

annotateTyp (RST.TyData loc pol xtors) = do 
  knd <- getXtorKinds loc xtors 
  xtors' <- mapM annotateXtorSig xtors
  return (TST.TyData loc pol knd xtors')

annotateTyp (RST.TyCodata loc pol xtors) = do 
  knd <- getXtorKinds loc xtors
  xtors' <- mapM annotateXtorSig xtors
  return (TST.TyCodata loc pol knd xtors')

annotateTyp (RST.TyDataRefined loc pol tyn xtors) = do 
  xtors' <- mapM annotateXtorSig xtors
  knd <- getTyNameKind loc tyn
  return (TST.TyDataRefined loc pol knd tyn xtors')

annotateTyp (RST.TyCodataRefined loc pol tyn xtors) = do
  xtors' <- mapM annotateXtorSig xtors
  knd <- getTyNameKind loc tyn
  return (TST.TyCodataRefined loc pol knd tyn xtors')

annotateTyp (RST.TyNominal loc pol tyn vartys) = do
  vartys' <- mapM annotateVariantType vartys
  knd <- getTyNameKind loc tyn
  return (TST.TyNominal loc pol knd tyn vartys')

annotateTyp (RST.TySyn loc pol tn ty) = do 
  ty' <- annotateTyp ty 
  return (TST.TySyn loc pol tn ty')

annotateTyp (RST.TyBot loc) = TST.TyBot loc . KindVar <$> newKVar

annotateTyp (RST.TyTop loc) = TST.TyTop loc . KindVar <$> newKVar

annotateTyp (RST.TyUnion loc ty1 ty2) = do 
  ty1' <- annotateTyp ty1
  ty2' <- annotateTyp ty2
  kv <- newKVar 
  return (TST.TyUnion loc (KindVar kv) ty1' ty2')
  
annotateTyp (RST.TyInter loc ty1 ty2) = do
  ty1' <- annotateTyp ty1
  ty2' <- annotateTyp ty2
  kv <- newKVar 
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


