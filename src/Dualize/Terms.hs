module Dualize.Terms where

import Data.Text qualified as T

import Syntax.TST.Terms
import Syntax.Common
import Syntax.Common.TypesPol
import Utils

data DualizeError = DualPrim Loc String | DualPrint Loc String  | DualRead Loc String | DualPrimOp Loc PrimitiveOp String
  deriving Show

dualTerm :: PrdCnsRep pc -> Term pc -> Either DualizeError (Term (FlipPrdCns pc))
dualTerm rep (BoundVar _ _ ty i) = return $ BoundVar defaultLoc (flipPrdCns rep) (dualType' rep ty) i
dualTerm rep (FreeVar _ _ ty i) = return $ FreeVar defaultLoc (flipPrdCns rep) (dualType' rep ty) (dualFVName i)
dualTerm rep (Xtor _ annot pc ty ns xtor subst) = do 
    subst' <- dualSubst subst
    return $ Xtor defaultLoc (dualXtorAnnot annot) (flipPrdCns pc) (dualType' rep ty) ns (dualXtorName xtor) subst'
dualTerm rep (XCase _ annot pc ty ns cases) = do 
    cases' <- mapM dualCmdCase cases
    return $ XCase defaultLoc (dualMatchAnnot annot) (flipPrdCns pc) (dualType' rep ty) ns cases'
dualTerm rep (MuAbs _ annot pc ty fv cmd) = do
    cmd' <- dualCmd cmd
    return $ MuAbs defaultLoc (dualMuAnnot annot)  (flipPrdCns pc)  (dualType' rep ty) (dualFVName <$> fv) cmd'
dualTerm _ (PrimLitI64 loc i) = Left $ DualPrim loc $ "Cannot dualize integer literal: " ++ show i
dualTerm _ (PrimLitF64 loc i) = Left $ DualPrim loc $ "Cannot dualize floating point literal: " ++ show i

dualCmd :: Command -> Either DualizeError Command
dualCmd (Apply _ annot kind prd cns) = do
    t1 <- dualTerm CnsRep cns
    t2 <- dualTerm PrdRep prd
    return $ Apply defaultLoc (dualApplyAnnot annot) (dualMonoKind <$> kind) t1 t2
dualCmd (Print loc _ _) = Left $ DualPrint loc $ "Cannot dualize Print command"
dualCmd (Read loc _)  = Left $ DualRead loc $ "Cannot dualize Read command"
dualCmd (Jump _ fv)  = return $ Jump defaultLoc (dualFVName fv)
dualCmd (PrimOp loc _ op _) = Left $ DualPrimOp loc op "Cannot dualize primitive op"
dualCmd (ExitSuccess _) = return $ ExitSuccess defaultLoc
dualCmd (ExitFailure _) = return $ ExitFailure defaultLoc

dualCmdCase :: CmdCase -> Either DualizeError CmdCase
dualCmdCase (MkCmdCase _ pat cmd) = do
    cmd' <- dualCmd cmd
    return $ MkCmdCase defaultLoc (dualPattern pat) cmd'

flipPC :: PrdCns -> PrdCns
flipPC Prd = Cns
flipPC Cns = Prd

dualPattern :: Pattern -> Pattern
dualPattern (XtorPat _ xtor vars) = XtorPat defaultLoc (dualXtorName xtor) (map (\(pc,fv) -> (flipPC pc, dualFVName <$> fv)) vars)

dualSubst :: Substitution -> Either DualizeError Substitution
dualSubst subst = mapM dualPrdCnsTerm subst
  where
      dualPrdCnsTerm :: PrdCnsTerm -> Either DualizeError PrdCnsTerm
      dualPrdCnsTerm (PrdTerm t) = dualTerm PrdRep t >>= (return . CnsTerm)
      dualPrdCnsTerm (CnsTerm t) = dualTerm CnsRep t >>= (return . PrdTerm)

dualXtorName :: XtorName -> XtorName
dualXtorName (MkXtorName x) = MkXtorName (T.pack "Co" `T.append` x)

dualXtorAnnot :: XtorAnnot -> XtorAnnot
dualXtorAnnot XtorAnnotOrig = XtorAnnotOrig
dualXtorAnnot (XtorAnnotSemi i) = XtorAnnotDtor i
dualXtorAnnot (XtorAnnotDtor i) = XtorAnnotSemi i

dualApplyAnnot :: ApplyAnnot -> ApplyAnnot
dualApplyAnnot ApplyAnnotOrig = ApplyAnnotOrig
dualApplyAnnot ApplyAnnotSemi = ApplyAnnotDtor
dualApplyAnnot ApplyAnnotDtor = ApplyAnnotSemi
dualApplyAnnot ApplyAnnotCaseOfInner = ApplyAnnotCocaseOfInner
dualApplyAnnot ApplyAnnotCaseOfOuter = ApplyAnnotCocaseOfOuter
dualApplyAnnot ApplyAnnotCocaseOfInner = ApplyAnnotCaseOfInner
dualApplyAnnot ApplyAnnotCocaseOfOuter = ApplyAnnotCaseOfOuter
dualApplyAnnot (ApplyAnnotXCaseI i) = ApplyAnnotXCaseI i
dualApplyAnnot ApplyAnnotCaseOfCmd = ApplyAnnotCocaseOfCmd
dualApplyAnnot ApplyAnnotCocaseOfCmd = ApplyAnnotCaseOfCmd
dualApplyAnnot (ApplyAnnotXCaseOfIInner i) = ApplyAnnotXCaseOfIInner i
dualApplyAnnot ApplyAnnotCaseOfIOuter = ApplyAnnotCocaseOfIOuter
dualApplyAnnot ApplyAnnotCocaseOfIOuter = ApplyAnnotCaseOfIOuter


dualMatchAnnot :: MatchAnnot pc -> MatchAnnot (FlipPrdCns pc)
dualMatchAnnot MatchAnnotOrig = MatchAnnotOrig
dualMatchAnnot MatchAnnotCaseOf = MatchAnnotCocaseOf
dualMatchAnnot MatchAnnotCocaseOf = MatchAnnotCaseOf
dualMatchAnnot (MatchAnnotXCaseI pc) = MatchAnnotXCaseI (flipPrdCns pc)
dualMatchAnnot MatchAnnotCaseOfI = MatchAnnotCocaseOfI
dualMatchAnnot MatchAnnotCocaseOfI = MatchAnnotCaseOfI
dualMatchAnnot MatchAnnotCaseOfCmd = MatchAnnotCocaseOfCmd
dualMatchAnnot MatchAnnotCocaseOfCmd = MatchAnnotCaseOfCmd

dualMuAnnot :: MuAnnot -> MuAnnot
dualMuAnnot MuAnnotOrig = MuAnnotOrig
dualMuAnnot MuAnnotSemi = MuAnnotDtor
dualMuAnnot MuAnnotDtor = MuAnnotSemi
dualMuAnnot MuAnnotCaseOf = MuAnnotCocaseOf
dualMuAnnot MuAnnotCocaseOf = MuAnnotCaseOf

dualFVName :: FreeVarName -> FreeVarName
dualFVName (MkFreeVarName x) = MkFreeVarName (T.pack "co" `T.append` x)


dualType' :: PrdCnsRep pc -> Typ (PrdCnsToPol pc)  -> Typ (PrdCnsToPol (FlipPrdCns pc))
dualType' PrdRep t = dualType PosRep t
dualType' CnsRep t = dualType NegRep t

dualType :: PolarityRep pol -> Typ pol -> Typ (FlipPol pol)
dualType pol (TyVar _loc _ kind x) = TyVar defaultLoc (flipPolarityRep pol) (dualMonoKind <$> kind) x
dualType pol (TyNominal _ _ kind tn vtys) = TyNominal defaultLoc  (flipPolarityRep pol) (dualMonoKind <$> kind) (dualRnTypeName tn) (dualVariantType pol <$> vtys)
dualType pol (TyPrim loc _ pt) = TyPrim loc (flipPolarityRep pol) pt
-- @BinderDavid please check
dualType _ (TyBot loc mk) = TyTop loc mk  
dualType _ (TyTop loc mk) = TyBot loc mk  
dualType pol (TyUnion loc mk t1 t2) = TyInter loc mk (dualType pol t1) (dualType pol t2)
dualType pol (TyInter loc mk t1 t2) = TyUnion loc mk (dualType pol t1) (dualType pol t2)
dualType pol (TyRec loc p x t) = TyRec loc (flipPolarityRep p) x (dualType pol t)
dualType pol (TySyn loc _ rn ty) = TySyn loc (flipPolarityRep pol) (dualRnTypeName rn) (dualType pol ty)
dualType PosRep (TyData loc _ rn xtors) = TyCodata loc NegRep  (dualRnTypeName <$> rn) xtors 
dualType NegRep (TyData loc _ rn xtors) = TyCodata loc PosRep  (dualRnTypeName <$> rn) xtors 
dualType PosRep (TyCodata loc _ rn xtors) = TyData loc NegRep  (dualRnTypeName <$> rn) xtors 
dualType NegRep (TyCodata loc _ rn xtors) = TyData loc PosRep  (dualRnTypeName <$> rn) xtors 

dualVariantType :: PolarityRep pol -> VariantType pol -> VariantType (FlipPol pol)
dualVariantType pol (CovariantType ty) = CovariantType (dualType pol ty) 
dualVariantType PosRep (ContravariantType ty) = ContravariantType (dualType NegRep ty)
dualVariantType NegRep (ContravariantType ty) = ContravariantType (dualType PosRep ty)

dualRnTypeName :: RnTypeName -> RnTypeName
dualRnTypeName (MkRnTypeName _loc _doc mn tn) = MkRnTypeName defaultLoc Nothing mn (dualTypeName tn)

dualTypeName :: TypeName -> TypeName 
dualTypeName (MkTypeName tn) = MkTypeName $ T.pack "Co" `T.append` tn

dualMonoKind :: MonoKind -> MonoKind
dualMonoKind mk = mk

dualTypeScheme :: PolarityRep pol ->TypeScheme pol -> TypeScheme (FlipPol pol)
dualTypeScheme pol (TypeScheme _  ts_vars ty) = TypeScheme defaultLoc ts_vars (dualType pol ty)