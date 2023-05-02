module TypeInference.GenerateConstraints.Terms
  ( GenConstraints(..)
  , genConstraintsTermRecursive
  ) where
import Debug.Trace
import Control.Monad.Reader
import Errors
import Data.List.NonEmpty (NonEmpty((:|)))
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..), Variance(..), PolyKind(..), EvaluationOrder)
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Program qualified as TST
import Syntax.TST.Types qualified as TST
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Program qualified as Core
import Syntax.RST.Types qualified as RST
import Syntax.RST.Types (Polarity(..), PolarityRep(..))
import Syntax.RST.Program qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Names
import Syntax.RST.Names
import Syntax.RST.Kinds
import Translate.EmbedTST (EmbedTST(..))
import Pretty.Pretty
import Data.List.NonEmpty qualified as NE
import Data.List (elemIndex)

import TypeInference.GenerateConstraints.Definition
import TypeInference.GenerateConstraints.Kinds
import TypeInference.Constraints
import TypeInference.SolveConstraints (resolveInstanceAnnot)
import Loc
import TypeInference.Environment
import TypeInference.GenerateConstraints.Primitives (primOps)
import Syntax.RST.Program (ClassDeclaration(classdecl_kinds))
import Syntax.TST.Terms (Substitution(..))

---------------------------------------------------------------------------------------------
-- Substitutions and Linear Contexts
---------------------------------------------------------------------------------------------

instance GenConstraints Core.PrdCnsTerm TST.PrdCnsTerm where
  genConstraints :: Core.PrdCnsTerm
                 -> GenM TST.PrdCnsTerm
  genConstraints (Core.PrdTerm tm) = TST.PrdTerm <$> genConstraints tm
  genConstraints (Core.CnsTerm tm) = TST.CnsTerm <$> genConstraints tm

instance GenConstraints Core.Substitution TST.Substitution where
  genConstraints :: Core.Substitution
                 -> GenM TST.Substitution
  genConstraints = fmap MkSubstitution . mapM genConstraints . (\x -> x.unSubstitution)

genConstraintsCtxts :: TST.LinearContext Pos -> TST.LinearContext Neg -> ConstraintInfo -> GenM ()
genConstraintsCtxts ctx1 ctx2 info | length ctx1 /= length ctx2 = do
  loc <- asks ((\x -> x.location) . snd)
  throwGenError (LinearContextsUnequalLength loc info ctx1 ctx2)
genConstraintsCtxts [] [] _ = return ()

genConstraintsCtxts ((TST.PrdCnsType PrdRep ty1) : rest1) (TST.PrdCnsType PrdRep ty2 : rest2) info = do
  addConstraint $ SubType info ty1 ty2
  addConstraint $ KindEq KindConstraint (TST.getKind ty1) (TST.getKind ty2)
  genConstraintsCtxts rest1 rest2 info

genConstraintsCtxts ((TST.PrdCnsType CnsRep ty1) : rest1) (TST.PrdCnsType CnsRep ty2 : rest2) info = do
  addConstraint $ SubType info ty2 ty1
  addConstraint $ KindEq KindConstraint (TST.getKind ty1) (TST.getKind ty2)
  genConstraintsCtxts rest1 rest2 info

genConstraintsCtxts (TST.PrdCnsType PrdRep _:_) (TST.PrdCnsType CnsRep _:_) info = do
  loc <- asks ((\x -> x.location) . snd)
  throwGenError (LinearContextIncompatibleTypeMode loc Prd info)
genConstraintsCtxts (TST.PrdCnsType CnsRep _:_) (TST.PrdCnsType PrdRep _:_) info = do
  loc <- asks ((\x -> x.location) . snd)
  throwGenError (LinearContextIncompatibleTypeMode loc Cns info)
genConstraintsCtxts ctx1@[] ctx2@(_:_) info = do
  loc <- asks ((\x -> x.location) . snd)
  throwGenError (LinearContextsUnequalLength loc info ctx1 ctx2)
genConstraintsCtxts ctx1@(_:_) ctx2@[] info = do
  loc <- asks ((\x -> x.location) . snd)
  throwGenError (LinearContextsUnequalLength loc info ctx1 ctx2)

---------------------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------------------

-- | Generate the constraints for a given Term.
instance GenConstraints (Core.Term pc) (TST.Term pc) where
  genConstraints :: Core.Term pc
                 -> GenM (TST.Term pc)
  --
  -- Bound variables:
  --
  -- Bound variables can be looked up in the context.
  --
  genConstraints (Core.BoundVar loc rep idx) = do
    ty <- lookupContext loc rep idx
    return (TST.BoundVar loc rep ty idx)
  --
  -- Free variables:
  --
  -- Free variables can be looked up in the environment,
  -- where they correspond to typing schemes. This typing
  -- scheme has to be instantiated with fresh unification variables.
  --
  genConstraints (Core.FreeVar loc rep v) = do
    tys <- snd <$> lookupTerm loc rep v
    ty <- instantiateTypeScheme v loc tys
    return (TST.FreeVar loc rep ty v)
  --
  -- Structural Xtors:
  --
  genConstraints (Core.Xtor loc annot rep RST.Structural xt subst) = do
    inferredSubst <- genConstraints subst
    let substTypes = TST.getTypArgs inferredSubst
    case rep of
      PrdRep -> do
        let rstty = RST.TyData defaultLoc PosRep [RST.MkXtorSig xt (embedTST <$> substTypes)]
        tstty <- annotateKind rstty
        return $ TST.Xtor loc annot rep tstty RST.Structural xt inferredSubst
      CnsRep -> do 
        let rstty = RST.TyCodata defaultLoc NegRep [RST.MkXtorSig xt (embedTST <$> substTypes)]
        tstty <- annotateKind rstty
        return $ TST.Xtor loc annot rep tstty RST.Structural xt inferredSubst
  --
  -- Nominal Xtors
  --
  genConstraints (Core.Xtor loc annot rep (RST.Nominal _) xt subst) = do
    -- First we infer the types of the arguments.
    substInferred <- genConstraints subst
    let substTypes = TST.getTypArgs substInferred
    -- Secondly we look up the argument types of the xtor in the type declaration.
    decl <- lookupDataDecl loc xt
    xtorSig <- lookupXtorSig loc xt NegRep
    -- Generate fresh unification variables for type parameters
    (args, tyParamsMap) <- freshTVarsForTypeParams (prdCnsToPol rep) decl
    -- Substitute these for the type parameters in the constructor signature
    let sig_args' = TST.zonk TST.SkolemRep tyParamsMap xtorSig.sig_args
    -- Then we generate constraints between the inferred types of the substitution
    -- and the types we looked up, i.e. the types declared in the XtorSig.
    genConstraintsCtxts substTypes sig_args' (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
    let nomTy rep = TST.TyNominal defaultLoc rep decl.data_kind decl.data_name
    if length args /= length decl.data_kind.kindArgs then
      throwOtherError loc ["Nominal Type " <> ppPrint decl.data_name <> " was not fully applied"]
    else do
      let ty = case args of [] -> nomTy; (fst:rst) -> \rep -> TST.TyApp defaultLoc rep decl.data_kind.returnKind (nomTy rep) decl.data_name (fst:|rst)
      case rep of
        PrdRep -> return (TST.Xtor loc annot rep (ty PosRep) (RST.Nominal decl.data_name.rnTnName) xt substInferred)
        CnsRep -> return (TST.Xtor loc annot rep (ty NegRep) (RST.Nominal decl.data_name.rnTnName) xt substInferred)

  --
  -- Refinement Xtors
  --
  genConstraints (Core.Xtor loc annot rep RST.Refinement xt subst) = do
    -- First we infer the types of the arguments.
    substInferred <- genConstraints subst
    -- Secondly we look up the argument types of the xtor in the type declaration.
    let substTypes = TST.getTypArgs substInferred    
    -- Since we infer refinement types, we have to look up the translated xtorSig.
    decl <- lookupDataDecl loc xt
    let pk = decl.data_kind
    (argVars,skolemSubst) <- freshSkolems pk
    xtorSigUpper <- lookupXtorSigUpper loc xt 
    xtorSigUpper' <- freshSkolemsXtor xtorSigUpper skolemSubst
    (uvarsPos,uvarsNeg,_) <- getTypeArgsRef loc decl argVars
    let cstrInfo = case rep of PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc
--    addUVConstr (uvarsPos,uvarsNeg) cstrInfo (zip argVars ((\(_,_,mk) -> mk) <$> pk.kindArgs))
    -- Then we generate constraints between the inferred types of the substitution
    let constrSigArgs = TST.zonk TST.SkolemRep skolemSubst xtorSigUpper'.sig_args 
    let (pairsPos,pairsNeg) = TST.getDeclReplacements xtorSigUpper'.sig_args substTypes 
    substTypes' <- forM substTypes (\ty -> do 
      let replacedPos = foldr (\(tyPos,sk) -> TST.replType PosRep sk tyPos) ty pairsPos
      let replacedNeg = foldr (\(tyNeg,sk) -> TST.replType NegRep sk tyNeg) replacedPos pairsNeg
      return replacedNeg)
    forM_ pairsPos (\(ty,sk) -> 
      case elemIndex sk argVars of 
        Nothing -> return ()
        Just i -> do
          let uvars = varTyToTy (uvarsPos !! i,uvarsNeg !! i)
          addConstraint $ SubType cstrInfo ty (snd uvars))
    forM_ pairsNeg (\(ty,sk) -> 
      case elemIndex sk argVars of 
        Nothing -> return ()
        Just i -> do
          let uvars = varTyToTy (uvarsPos !! i,uvarsNeg !! i)
          addConstraint $ SubType cstrInfo (fst uvars) ty)
    trace ("substTypes " <> ppPrintString substTypes <> 
           "\n xtorsig "<> ppPrintString xtorSigUpper' <> 
           "\n replaced " <> ppPrintString substTypes'<> 
           "\n replacement " <> concatMap (\(ty,sk) -> ppPrintString ty <> " -> " <> show sk) pairsPos <> 
           "\n" <> concatMap (\(ty,sk) -> ppPrintString ty <> " -> " <> show sk) pairsNeg) $ pure ()
    genConstraintsCtxts substTypes' constrSigArgs cstrInfo
    let newXtorSig = [TST.MkXtorSig xt substTypes']
    case rep of 
      PrdRep -> do 
        let refTy = TST.TyDataRefined defaultLoc PosRep pk argVars decl.data_name newXtorSig
        let ty = getAppTy PosRep pk.returnKind decl.data_name (uvarsPos,uvarsNeg) refTy
        return $ TST.Xtor loc annot rep ty RST.Refinement xt substInferred
      CnsRep -> do
        let refTy = TST.TyCodataRefined defaultLoc NegRep pk argVars decl.data_name newXtorSig
        let ty = getAppTy NegRep pk.returnKind decl.data_name (uvarsPos,uvarsNeg) refTy
        return $ TST.Xtor loc annot rep ty RST.Refinement xt substInferred
    where 
--      replaceArgs :: TST.PrdCnsType pol -> TST.PrdCnsType pol -> ([TST.VariantType Pos],[TST.VariantType Neg]) -> [SkolemTVar] -> GenM (TST.PrdCnsType pol)
--      replaceArgs substType xtorType (argsPos,argsNeg) argVars = do 
--        let newArgs = varTyToTy <$> zip argsPos argsNeg
--        case substType of 
--          TST.PrdCnsType PrdRep ty -> do
--            let posReplaced = foldr (\(arg,sk) -> TST.replType PosRep sk arg) ty (zip (fst <$> newArgs) argVars)
--            let negReplaced = foldr (\(arg,sk) -> TST.replType NegRep sk arg) posReplaced (zip (snd <$> newArgs) argVars)
--            pure $ TST.PrdCnsType PrdRep negReplaced
--          TST.PrdCnsType CnsRep ty -> do
--            let posReplaced = foldr (\(arg,sk) -> TST.replType PosRep sk arg) ty (zip (fst <$> newArgs) argVars)
--            let negReplaced = foldr (\(arg,sk) -> TST.replType NegRep sk arg) posReplaced (zip (snd <$> newArgs) argVars)
--            pure $ TST.PrdCnsType CnsRep negReplaced 

      varTyToTy :: (TST.VariantType Pos, TST.VariantType Neg) -> (TST.Typ Pos,TST.Typ Neg)
      varTyToTy (TST.CovariantType tyPos, TST.CovariantType tyNeg) = (tyPos,tyNeg)
      varTyToTy (TST.ContravariantType tyNeg,TST.ContravariantType tyPos) = (tyPos,tyNeg)
      varTyToTy _ = error "impossible"

--      addUVConstr :: ([TST.VariantType Pos],[TST.VariantType Neg]) -> ConstraintInfo -> [(SkolemTVar,MonoKind)] -> GenM()
--      addUVConstr (uvpos,uvneg) info skolems = if length uvpos == length skolems then do 
--        let skolemsNeg = (\(sk,mk) -> TST.TySkolemVar defaultLoc NegRep (monoToAnyKind mk) sk) <$> skolems
--        let uvs = varTyToTy <$> zip uvpos uvneg
--        forM_ (zip uvs skolemsNeg) (\(uv,sk) -> addConstraint $ SubType info uv sk)
--        else 
--          throwOtherError defaultLoc ["Number of skolems does not match number of generated unification variables"]
      getAppTy :: PolarityRep pol -> EvaluationOrder -> RnTypeName -> ([TST.VariantType Pos],[TST.VariantType Neg]) -> (TST.Typ pol -> TST.Typ pol)
      getAppTy _ _ _ ([],[]) = id
      getAppTy _ _ _ ([],_) = error "impossible"
      getAppTy _ _ _ (_,[]) = error "impossible"
      getAppTy PosRep eo tyn (fstPos:rstPos,_) = \x -> TST.TyApp defaultLoc PosRep eo x tyn (fstPos:|rstPos)
      getAppTy NegRep eo tyn (_,fstNeg:rstNeg) = \x -> TST.TyApp defaultLoc NegRep eo x tyn (fstNeg:|rstNeg)

  --
  -- Structural pattern and copattern matches:
  --
  genConstraints (Core.XCase loc annot rep RST.Structural cases) = do
    inferredCases <- forM cases (\(Core.MkCmdCase cmdcase_loc (Core.XtorPat loc xt args) cmdcase_cmd) -> do
                        -- Generate positive and negative unification variables for all variables
                        -- bound in the pattern.
                        xtor <- lookupStructuralXtor xt
                        let argKnds = map snd xtor.strxtordecl_arity
                        let tVarArgs = zipWith (curry (\ ((x, y), z) -> (x, y, monoToAnyKind z))) args argKnds
                        (uvarsPos, uvarsNeg) <- freshTVars tVarArgs
                        -- Check the command in the context extended with the positive unification variables
                        cmdInferred <- withContext uvarsPos (genConstraints cmdcase_cmd)
                        -- Return the negative unification variables in the returned type.
                        return (TST.MkCmdCase cmdcase_loc (Core.XtorPat loc xt args) cmdInferred, TST.MkXtorSig xt uvarsNeg))
    let xtors = snd <$> inferredCases
    case rep of
      -- The return type is a structural type consisting of a XtorSig for each case.
      PrdRep -> do 
        let rstty = RST.TyCodata defaultLoc PosRep (embedTST <$> xtors)
        tstty <- annotateKind rstty
        return $ TST.XCase loc annot rep tstty RST.Structural (fst <$> inferredCases)
      CnsRep -> do
        let rstty = RST.TyData defaultLoc NegRep (embedTST <$> xtors)
        tstty <- annotateKind rstty
        return $ TST.XCase loc annot rep tstty RST.Structural (fst <$> inferredCases)
  --
  -- Nominal pattern and copattern matches
  --
  genConstraints (Core.XCase loc _ _ (RST.Nominal _) []) =
    -- We know that empty matches cannot be parsed as nominal.
    -- It is therefore safe to pattern match on the head of the xtors in the other cases.
    throwGenError (EmptyNominalMatch loc)
  genConstraints (Core.XCase loc annot rep (RST.Nominal _) cases@(pmcase:_)) = do
    -- We lookup the data declaration based on the first pattern match case.
    decl <- lookupDataDecl loc (case pmcase.cmdcase_pat of (Core.XtorPat _ xt _) -> xt)
    -- We check that all cases in the pattern match belong to the type declaration.
    checkCorrectness loc ((\cs -> case cs.cmdcase_pat of Core.XtorPat _ xt _ -> xt) <$> cases) decl
    -- We check that all xtors in the type declaration are matched against.
    checkExhaustiveness loc ((\cs -> case cs.cmdcase_pat of Core.XtorPat _ xt _ -> xt) <$> cases) decl
    -- Generate fresh unification variables for type parameters
    (args, tyParamsMap) <- freshTVarsForTypeParams (prdCnsToPol rep) decl

    inferredCases <- forM cases (\(Core.MkCmdCase cmdcase_loc (Core.XtorPat loc' xt args) cmdcase_cmd) -> do
                    -- We lookup the types belonging to the xtor in the type declaration.
                    posTypes <- (\x -> x.sig_args) <$> lookupXtorSig loc xt PosRep
                    negTypes <- (\x -> x.sig_args) <$> lookupXtorSig loc xt NegRep
                    -- Substitute fresh unification variables for type parameters
                    let posTypes' = TST.zonk TST.SkolemRep tyParamsMap posTypes
                    let negTypes' = TST.zonk TST.SkolemRep tyParamsMap negTypes
                    -- We generate constraints for the command in the context extended
                    -- with the types from the signature.
                    cmdInferred <- withContext posTypes' (genConstraints cmdcase_cmd)
                    return (TST.MkCmdCase cmdcase_loc (Core.XtorPat loc' xt args) cmdInferred, TST.MkXtorSig xt negTypes'))
    let nomTy rep = TST.TyNominal defaultLoc rep decl.data_kind decl.data_name
    if length args /= length decl.data_kind.kindArgs then 
      throwOtherError loc ["Nominal Type " <> ppPrint decl.data_name <> " was not fully applied"]
    else do 
      let ty = case args of [] -> nomTy; (fst:rst) -> \rep -> TST.TyApp defaultLoc rep decl.data_kind.returnKind (nomTy rep) decl.data_name (fst:|rst)
      case rep of
        PrdRep -> return $ TST.XCase loc annot rep (ty PosRep) (RST.Nominal decl.data_name.rnTnName) (fst <$> inferredCases)
        CnsRep -> return $ TST.XCase loc annot rep (ty NegRep) (RST.Nominal decl.data_name.rnTnName) (fst <$> inferredCases)
  --
  -- Refinement pattern and copattern matches
  --
  genConstraints (Core.XCase loc _ _ RST.Refinement []) =
    -- We know that empty matches cannot be parsed as Refinement.
    -- It is therefore safe to pattern match on the head of the xtors in the other cases.
    throwGenError (EmptyRefinementMatch loc)
  genConstraints (Core.XCase loc annot rep RST.Refinement cases@(pmcase:_)) = do
    -- We lookup the data declaration based on the first pattern match case.
    decl <- lookupDataDecl loc (case pmcase.cmdcase_pat of (Core.XtorPat _ xt _) -> xt)
    -- We check that all cases in the pattern match belong to the type declaration.
    checkCorrectness loc ((\cs -> case cs.cmdcase_pat of Core.XtorPat _ xt _ -> xt) <$> cases) decl
    -- Generate fresh unification variables for type parameters
    (argVars,skolemSubst) <- freshSkolems decl.data_kind
    (tyArgsPos,tyArgsNeg,argSubst) <- getTypeArgsRef loc decl argVars
    inferredCases <- forM cases (\(Core.MkCmdCase cmdcase_loc (Core.XtorPat loc xt args) cmdcase_cmd) -> do
                        -- Generate positive and negative unification variables for all variables
                        -- bound in the pattern.
                        -- Check the command in the context extended with the positive unification variables
                        -- We have to bound the unification variables with the lower and upper bounds generated
                        -- from the information in the type declaration. These lower and upper bounds correspond
                        -- to the least and greatest type translation.
                        -- Then we generate constraints between the inferred types of the substitution
                        -- For the type, we return the unification variables which are now bounded by the least
                        -- and greatest type translation.

                        xtor <- lookupXtorSig loc xt PosRep 
                        xtor' <- freshSkolemsXtor xtor skolemSubst
                        xtorLower <- lookupXtorSigLower loc xt
                        xtorLower' <- freshSkolemsXtor xtorLower skolemSubst
                        xtorUpper <- lookupXtorSigUpper loc xt 
                        xtorUpper' <- freshSkolemsXtor xtorUpper skolemSubst

                        case argVars of 
                          [] -> do 
                            let argKnds = map TST.getKind xtor'.sig_args
                            let tVarArgs = zipWith (curry (\ ((x, y), z) -> (x, y, z))) args argKnds
                            (substTypesPos, substTypesNeg) <- freshTVars tVarArgs
                            cmdInferred <- withContext substTypesPos (genConstraints cmdcase_cmd)
                            genConstraintsCtxts xtorLower'.sig_args substTypesNeg (PatternMatchConstraint loc)
                            genConstraintsCtxts substTypesPos xtorUpper'.sig_args (PatternMatchConstraint loc)
                            return (TST.MkCmdCase cmdcase_loc (Core.XtorPat loc xt args) cmdInferred, TST.MkXtorSig xt substTypesNeg)
                          (skFst:skRst) -> do
                            let skolems = skFst :| skRst
                            tyArgs <- getSkArgs loc decl.data_kind skolems
                            let xtor'' = TST.zonk TST.SkolemRep skolemSubst xtor'
                            prdCnsTys <- forM (zip args xtor''.sig_args) (freshTVarRef loc tyArgs)
                            let (substTypesPos,substTypesNeg) = (fst <$> prdCnsTys,snd <$> prdCnsTys)
                            let lowerBound = TST.zonk TST.SkolemRep skolemSubst xtorLower'.sig_args
                            let upperBound = TST.zonk TST.SkolemRep skolemSubst xtorUpper'.sig_args
                            genConstraintsCtxts lowerBound substTypesNeg (PatternMatchConstraint loc)
                            genConstraintsCtxts substTypesPos upperBound (PatternMatchConstraint loc)
                            let substTypesPos' = TST.zonk TST.SkolemRep argSubst substTypesPos
                            cmdInferred <- withContext substTypesPos' (genConstraints cmdcase_cmd)
                            return (TST.MkCmdCase cmdcase_loc (Core.XtorPat loc xt args) cmdInferred, TST.MkXtorSig xt substTypesNeg))
    case rep of
      CnsRep -> do
        let refTy = TST.TyDataRefined defaultLoc NegRep decl.data_kind argVars decl.data_name (snd <$> inferredCases)
        let ty = case tyArgsNeg of [] -> refTy; (fst:rst) -> TST.TyApp defaultLoc NegRep decl.data_kind.returnKind refTy decl.data_name (fst:|rst)

        return $ TST.XCase loc annot rep ty RST.Refinement (fst <$> inferredCases)
      PrdRep -> do
        let refTy = TST.TyCodataRefined defaultLoc PosRep decl.data_kind argVars decl.data_name (snd <$> inferredCases)
        let ty = case tyArgsPos of [] -> refTy; (fst:rst) -> TST.TyApp defaultLoc PosRep decl.data_kind.returnKind refTy decl.data_name (fst:|rst)

        return $ TST.XCase loc annot rep ty RST.Refinement (fst <$> inferredCases)
     where  
      getSkArgs :: Loc -> PolyKind -> NonEmpty SkolemTVar -> GenM (NonEmpty (TST.VariantType Pos), NonEmpty (TST.VariantType Neg))
      getSkArgs loc pk skolems = if length pk.kindArgs == length skolems then do 
        let kndVar = case (\(x,_,z) -> (x,z)) <$> pk.kindArgs of [] -> error "impossible"; pairFst:pairRst -> pairFst :| pairRst 
        skArgs <- forM (NE.zip kndVar skolems) (\((var,mk),sk) -> do 
          let skPos = TST.TySkolemVar defaultLoc PosRep (monoToAnyKind mk) sk
          let skNeg = TST.TySkolemVar defaultLoc NegRep (monoToAnyKind mk) sk
          case var of 
            Covariant -> return (TST.CovariantType skPos,TST.CovariantType skNeg)
            Contravariant -> return (TST.ContravariantType skNeg, TST.ContravariantType skPos)
          )
        return (fst <$> skArgs, snd <$> skArgs)
      else 
        throwOtherError loc ["bound skolem vars don't match polykind"]
      freshTVarRef :: Loc -> (NonEmpty (TST.VariantType Pos), NonEmpty (TST.VariantType Neg)) -> ((PrdCns,Maybe FreeVarName),TST.PrdCnsType pol) -> GenM (TST.PrdCnsType Pos,TST.PrdCnsType Neg)
      freshTVarRef loc _ ((Prd,_),TST.PrdCnsType CnsRep _) = throwOtherError loc ["Xtor argument has to be consumer, was producer"]
      freshTVarRef loc _ ((Cns,_),TST.PrdCnsType PrdRep _) = throwOtherError loc ["Xtor argument has to be consumer, was producer"]
      freshTVarRef _ argTys ((Prd,fv),TST.PrdCnsType PrdRep ty) = case ty of 
        TST.TyApp loc' _ eo ty tyn _ -> do
          (tyPos, tyNeg) <- freshTVar (ProgramVariable (fromMaybeVar fv)) (Just (TST.getKind ty))
          let newTyPos = TST.TyApp loc' PosRep eo tyPos tyn (fst argTys)
          let newTyNeg = TST.TyApp loc' NegRep eo tyNeg tyn (snd argTys)
          return (TST.PrdCnsType PrdRep newTyPos, TST.PrdCnsType PrdRep newTyNeg) 
        uvPos@(TST.TyUniVar loc PosRep knd uv) -> do 
          let uvNeg = TST.TyUniVar loc NegRep knd uv
          return (TST.PrdCnsType PrdRep uvPos, TST.PrdCnsType PrdRep uvNeg)
        uvNeg@(TST.TyUniVar loc NegRep knd uv) -> do 
          let uvPos = TST.TyUniVar loc PosRep knd uv 
          return (TST.PrdCnsType PrdRep uvPos, TST.PrdCnsType PrdRep uvNeg)
        skPos@(TST.TySkolemVar loc PosRep pk sk) -> do 
          let skNeg = TST.TySkolemVar loc NegRep pk sk
          return (TST.PrdCnsType PrdRep skPos, TST.PrdCnsType PrdRep skNeg)
        skNeg@(TST.TySkolemVar loc NegRep pk sk) -> do 
          let skPos = TST.TySkolemVar loc PosRep pk sk
          return (TST.PrdCnsType PrdRep skPos, TST.PrdCnsType PrdRep skNeg)
        _ -> do
          let knd = TST.getKind ty
          (tp, tn) <- freshTVar (ProgramVariable (fromMaybeVar fv)) (Just knd)
          return (TST.PrdCnsType PrdRep tp,TST.PrdCnsType PrdRep tn)
      freshTVarRef _ argTys ((Cns,fv),TST.PrdCnsType CnsRep ty) = case ty of 
        TST.TyApp loc' _ eo ty tyn _ -> do 
          (tyPos, tyNeg) <- freshTVar (ProgramVariable (fromMaybeVar fv)) (Just (TST.getKind ty))
          let newTyPos = TST.TyApp loc' PosRep eo tyPos tyn (fst argTys)
          let newTyNeg = TST.TyApp loc' NegRep eo tyNeg tyn (snd argTys)
          return (TST.PrdCnsType CnsRep newTyNeg, TST.PrdCnsType CnsRep newTyPos)
        uvPos@(TST.TyUniVar loc PosRep knd uv) -> do 
          let uvNeg = TST.TyUniVar loc NegRep knd uv
          return (TST.PrdCnsType CnsRep uvNeg, TST.PrdCnsType CnsRep uvPos)
        uvNeg@(TST.TyUniVar loc NegRep knd uv) -> do 
          let uvPos = TST.TyUniVar loc PosRep knd uv 
          return (TST.PrdCnsType CnsRep uvNeg, TST.PrdCnsType CnsRep uvPos)
        skPos@(TST.TySkolemVar loc PosRep pk sk) -> do 
          let skNeg = TST.TySkolemVar loc NegRep pk sk
          return (TST.PrdCnsType CnsRep skNeg, TST.PrdCnsType CnsRep skPos)
        skNeg@(TST.TySkolemVar loc NegRep pk sk) -> do 
          let skPos = TST.TySkolemVar loc PosRep pk sk
          return (TST.PrdCnsType CnsRep skNeg, TST.PrdCnsType CnsRep skPos)
        _ -> do 
          let knd = TST.getKind ty 
          (tp,tn) <- freshTVar (ProgramVariable (fromMaybeVar fv)) (Just knd)
          return (TST.PrdCnsType CnsRep tn, TST.PrdCnsType CnsRep tp)
   

  --
  -- Mu and TildeMu abstractions:
  --
  genConstraints (Core.MuAbs loc annot PrdRep bs cmd) = do
    (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs)) Nothing
    cmdInferred <- withContext [TST.PrdCnsType CnsRep uvneg] (genConstraints cmd)
    return (TST.MuAbs loc annot PrdRep uvpos bs cmdInferred)
  genConstraints (Core.MuAbs loc annot CnsRep bs cmd) = do
    (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs)) Nothing
    cmdInferred <- withContext [TST.PrdCnsType PrdRep uvpos] (genConstraints cmd)
    return (TST.MuAbs loc annot CnsRep uvneg bs cmdInferred)
  genConstraints (Core.PrimLitI64 loc i) = pure $ TST.PrimLitI64 loc i
  genConstraints (Core.PrimLitF64 loc d) = pure $ TST.PrimLitF64 loc d
  genConstraints (Core.PrimLitChar loc d) = pure $ TST.PrimLitChar loc d
  genConstraints (Core.PrimLitString loc d) = pure $ TST.PrimLitString loc d

instance GenConstraints Core.Command TST.Command where
  genConstraints :: Core.Command -> GenM TST.Command
  genConstraints (Core.ExitSuccess loc) =
    pure (TST.ExitSuccess loc)
  genConstraints (Core.ExitFailure loc) =
    pure (TST.ExitFailure loc)
  genConstraints (Core.Jump loc fv) = do
    -- Ensure that the referenced command is in scope
    _ <- lookupCommand loc fv
    pure (TST.Jump loc fv)
  genConstraints (Core.Method loc mn cn Nothing subst) = do
    decl <- lookupClassDecl loc cn
    insertSkolemsClass decl
      -- fresh type var and subsitution for type class variable(s)
    (tyParamsMap, uvs) <- createMethodSubst loc decl
    negTypes <- lookupMethodType loc mn decl NegRep
    ctxtNeg <- annotateKind negTypes
    let negTypes' = TST.zonk TST.SkolemRep tyParamsMap ctxtNeg 
    -- infer arg types
    substInferred <- genConstraints subst
    let substTypes = TST.getTypArgs substInferred
    genConstraintsCtxts substTypes negTypes' (TypeClassConstraint loc)
    case uvs of
      [] -> throwGenError (NoParamTypeClass loc)
      [uv] -> pure (TST.Method loc mn cn (TST.InstanceUnresolved uv) Nothing substInferred)
      _ -> throwGenError (MultiParamTypeClass loc)
  genConstraints (Core.Method loc mn cn (Just ty) subst) = do
    decl <- lookupClassDecl loc cn
    insertSkolemsClass decl
    case decl.classdecl_kinds.kindArgs of
      [] -> throwGenError (NoParamTypeClass loc)
      [(var, _, _)] -> do
        -- let resolvedType = (resolveType k typ, resolveType k tyn)
        resolvedType <- annotateKind ty
        -- generate kind constraints
        let tyParamsMap = paramsMap decl.classdecl_kinds.kindArgs [resolvedType]
        negTypes <- lookupMethodType loc mn decl NegRep
        ctxtNeg <- annotateKind negTypes
        let negTypes' = TST.zonk TST.SkolemRep tyParamsMap ctxtNeg 
        -- infer arg types
        substInferred <- genConstraints subst
        let substTypes = TST.getTypArgs substInferred
        genConstraintsCtxts substTypes negTypes' (TypeClassConstraint loc)
        env <- asks fst
        case var of
          Covariant -> case resolveInstanceAnnot PosRep (fst resolvedType) cn env of
            Right (inst,_,_) -> pure (TST.Method loc mn cn (TST.InstanceResolved inst) (Just resolvedType) substInferred)
            Left err -> throwGenError (InstanceResolution loc err)
          Contravariant -> case resolveInstanceAnnot NegRep (snd resolvedType) cn env of
            Right (inst,_,_) -> pure (TST.Method loc mn cn (TST.InstanceResolved inst) (Just resolvedType) substInferred)
            Left err -> throwGenError (InstanceResolution loc err)
      _ -> throwGenError (MultiParamTypeClass loc)
  genConstraints (Core.Print loc prd cmd) = do
    prd' <- genConstraints prd
    cmd' <- genConstraints cmd
    pure (TST.Print loc prd' cmd')
  genConstraints (Core.Read loc cns) = do
    cns' <- genConstraints cns
    peanoDecl <- lookupTypeName loc peanoNm
    let peanoKnd = peanoDecl.data_kind
    let cnsTy = TST.getTypeTerm cns'
    addConstraint (SubType (ReadConstraint loc)  (TST.TyNominal defaultLoc PosRep peanoKnd peanoNm) cnsTy)
    addConstraint $ KindEq KindConstraint (MkPknd peanoKnd) (TST.getKind cnsTy)
    return (TST.Read loc cns')
  genConstraints (Core.Apply loc annot t1 t2) = do
    t1' <- genConstraints t1
    t2' <- genConstraints t2
    let ty1 = TST.getTypeTerm t1'
    let ty2 = TST.getTypeTerm t2'
    addConstraint (SubType (CommandConstraint loc) ty1 ty2)
    addConstraint $ KindEq KindConstraint (TST.getKind ty1) (TST.getKind ty2)
    pure (TST.Apply loc annot (TST.getKind ty1) t1' t2')

  genConstraints (Core.PrimOp loc op subst) = do
    substInferred <- genConstraints subst
    let substTypes = TST.getTypArgs substInferred
    let sig = primOps op 
    sigs <- mapM annotateKind sig
    _ <- genConstraintsCtxts substTypes sigs (PrimOpArgsConstraint loc)
    pure (TST.PrimOp loc op substInferred)
  
instance GenConstraints Core.InstanceDeclaration TST.InstanceDeclaration where
  genConstraints :: Core.InstanceDeclaration -> GenM TST.InstanceDeclaration
  genConstraints idecl = do
    -- We lookup the class declaration  of the instance.
    cdecl <- lookupClassDecl idecl.instancedecl_loc idecl.instancedecl_class
    insertSkolemsClass cdecl
    -- We check that all implementations belong to the same type class.
    checkInstanceCoverage idecl.instancedecl_loc cdecl ((\(Core.XtorPat _ xt _) -> MkMethodName xt.unXtorName) . (\x -> x.instancecase_pat) <$> idecl.instancedecl_cases) 
    -- Generate fresh unification variables for type parameters
    instancety <- annotateKind idecl.instancedecl_typ
    let tyParamsMap = paramsMap cdecl.classdecl_kinds.kindArgs [instancety] 
    inferredCases <- forM idecl.instancedecl_cases (\(Core.MkInstanceCase instancecase_loc (Core.XtorPat loc xt args) instancecase_cmd) -> do
                    let mn :: MethodName = MkMethodName xt.unXtorName
                    -- We lookup the types belonging to the xtor in the type declaration.
                    posTypes <- lookupMethodType instancecase_loc mn cdecl PosRep
                    negTypes <- lookupMethodType instancecase_loc mn cdecl NegRep  
                    ctxtPos <- annotateKind posTypes
                    ctxtNeg <- annotateKind negTypes
                    -- Substitute fresh unification variables for type parameters
                    let posTypes' = TST.zonk TST.SkolemRep tyParamsMap ctxtPos 
                    let negTypes' = TST.zonk TST.SkolemRep tyParamsMap ctxtNeg 
                    -- We generate constraints for the command in the context extended
                    -- with the types from the signature.
                    cmdInferred <- withContext posTypes' (genConstraints instancecase_cmd)
                    genConstraintsCtxts posTypes' negTypes' (InstanceConstraint instancecase_loc)
                    pure TST.MkInstanceCase { instancecase_loc = instancecase_loc
                                            , instancecase_pat = Core.XtorPat loc xt args
                                            , instancecase_cmd = cmdInferred
                                            })
    pure TST.MkInstanceDeclaration { instancedecl_loc = idecl.instancedecl_loc
                                   , instancedecl_doc = idecl.instancedecl_doc
                                   , instancedecl_name = idecl.instancedecl_name
                                   , instancedecl_class = idecl.instancedecl_class
                                   , instancedecl_typ = instancety
                                   , instancedecl_cases = inferredCases
                                   }



---------------------------------------------------------------------------------------------
-- Checking recursive terms
---------------------------------------------------------------------------------------------

genConstraintsTermRecursive :: ModuleName
                            -> Loc
                            -> FreeVarName
                            -> PrdCnsRep pc -> Core.Term pc
                            -> GenM (TST.Term pc)
genConstraintsTermRecursive mn loc fv PrdRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv) Nothing
  tm <- withTerm mn PrdRep fv (TST.FreeVar loc PrdRep x fv) loc (TST.TypeScheme loc [] x) (genConstraints tm)
  let xTy = TST.getTypeTerm tm
  addConstraint (SubType RecursionConstraint xTy y)
  addConstraint $ KindEq KindConstraint (TST.getKind xTy) (TST.getKind y)
  return tm
genConstraintsTermRecursive mn loc fv CnsRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv) Nothing
  tm <- withTerm mn CnsRep fv (TST.FreeVar loc CnsRep y fv) loc (TST.TypeScheme loc [] y) (genConstraints tm)
  let yTy = TST.getTypeTerm tm
  addConstraint (SubType RecursionConstraint x yTy)
  addConstraint $ KindEq KindConstraint (TST.getKind x) (TST.getKind yTy)
  return tm
