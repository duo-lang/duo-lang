module Dualize.Terms where

import Data.Text qualified as T
import Data.Bifunctor ( Bifunctor(bimap) )
import Data.Functor ( (<&>) )

import Syntax.TST.Terms
import Syntax.TST.Types
import Syntax.Core.Annot
import Syntax.CST.Names
import Syntax.RST.Terms (PrimitiveOp)
import Syntax.CST.Kinds
import Syntax.RST.Types (FlipPol, FlipPrdCns, PolarityRep(..), flipPolarityRep, flipPrdCns)
import Syntax.CST.Types (PrdCnsRep(..), PrdCns(..))
import Syntax.RST.Program (PrdCnsToPol)
import Utils

data DualizeError
    = DualPrim Loc String 
    | DualPrint Loc String  
    | DualRead Loc String 
    | DualPrimOp Loc PrimitiveOp String 
    | DualMethod Loc String
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
dualTerm _ (PrimLitChar loc i) = Left $ DualPrim loc $ "Cannot dualize character literal: " ++ show i
dualTerm _ (PrimLitString loc i) = Left $ DualPrim loc $ "Cannot dualize string literal: " ++ show i

dualCmd :: Command -> Either DualizeError Command
dualCmd (Apply _ annot kind prd cns) = do
    t1 <- dualTerm CnsRep cns
    t2 <- dualTerm PrdRep prd
    return $ Apply defaultLoc (dualApplyAnnot annot) (dualMonoKind <$> kind) t1 t2
dualCmd (Print loc _ _) = Left $ DualPrint loc "Cannot dualize Print command"
dualCmd (Read loc _)  = Left $ DualRead loc "Cannot dualize Read command"
dualCmd (Jump _ fv)  = return $ Jump defaultLoc (dualFVName fv)
dualCmd (Method loc _ _ _) = Left $ DualMethod loc "Cannot dualize type class method"
dualCmd (PrimOp loc op _) = Left $ DualPrimOp loc op "Cannot dualize primitive op"
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
dualPattern (XtorPat _ xtor vars) = XtorPat defaultLoc (dualXtorName xtor) (map (bimap flipPC (dualFVName <$>)) vars)

dualSubst :: Substitution -> Either DualizeError Substitution
dualSubst = mapM dualPrdCnsTerm
  where
      dualPrdCnsTerm :: PrdCnsTerm -> Either DualizeError PrdCnsTerm
      dualPrdCnsTerm (PrdTerm t) = dualTerm PrdRep t <&> CnsTerm
      dualPrdCnsTerm (CnsTerm t) = dualTerm CnsRep t <&> PrdTerm

dualXtorName :: XtorName -> XtorName
dualXtorName (MkXtorName (T.stripPrefix "Co" -> Just n)) | T.length n > 0 = MkXtorName n
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
dualApplyAnnot ApplyAnnotLambda = ApplyAnnotLambda

dualMatchAnnot :: MatchAnnot pc -> MatchAnnot (FlipPrdCns pc)
dualMatchAnnot MatchAnnotOrig = MatchAnnotOrig
dualMatchAnnot MatchAnnotCaseOf = MatchAnnotCocaseOf
dualMatchAnnot MatchAnnotCocaseOf = MatchAnnotCaseOf
dualMatchAnnot (MatchAnnotXCaseI pc) = MatchAnnotXCaseI (flipPrdCns pc)
dualMatchAnnot MatchAnnotCaseOfI = MatchAnnotCocaseOfI
dualMatchAnnot MatchAnnotCocaseOfI = MatchAnnotCaseOfI
dualMatchAnnot MatchAnnotCaseOfCmd = MatchAnnotCocaseOfCmd
dualMatchAnnot MatchAnnotCocaseOfCmd = MatchAnnotCaseOfCmd
dualMatchAnnot MatchAnnotLambda = MatchAnnotLambda

dualMuAnnot :: MuAnnot -> MuAnnot
dualMuAnnot MuAnnotOrig = MuAnnotOrig
dualMuAnnot MuAnnotSemi = MuAnnotDtor
dualMuAnnot MuAnnotDtor = MuAnnotSemi
dualMuAnnot MuAnnotCaseOf = MuAnnotCocaseOf
dualMuAnnot MuAnnotCocaseOf = MuAnnotCaseOf

dualFVName :: FreeVarName -> FreeVarName
dualFVName (MkFreeVarName (T.stripPrefix "co" -> Just n)) | T.length n > 0 = MkFreeVarName n
dualFVName (MkFreeVarName x) = MkFreeVarName (T.pack "co" `T.append` x)


dualType' :: PrdCnsRep pc -> Typ (PrdCnsToPol pc)  -> Typ (PrdCnsToPol (FlipPrdCns pc))
dualType' PrdRep t = dualType PosRep t
dualType' CnsRep t = dualType NegRep t

dualType :: PolarityRep pol -> Typ pol -> Typ (FlipPol pol)
dualType pol (TyUniVar _loc _ kind x) = TyUniVar defaultLoc (flipPolarityRep pol) (dualMonoKind <$> kind) x
dualType pol (TySkolemVar _loc _ kind x) = TySkolemVar defaultLoc (flipPolarityRep pol) (dualMonoKind <$> kind) x
dualType pol (TyRecVar _loc _ kind x) = TyRecVar defaultLoc (flipPolarityRep pol) (dualMonoKind <$> kind) x
dualType pol (TyNominal _ _ kind tn vtys) = TyNominal defaultLoc  (flipPolarityRep pol) (dualMonoKind <$> kind) (dualRnTypeName tn) (dualVariantType pol <$> vtys)
dualType pol (TyI64 loc _ ) = TyI64 loc (flipPolarityRep pol)
dualType pol (TyF64 loc _ ) = TyF64 loc (flipPolarityRep pol)
dualType pol (TyChar loc _ ) = TyChar loc (flipPolarityRep pol)
dualType pol (TyString loc _ ) = TyString loc (flipPolarityRep pol)
-- @BinderDavid please check
dualType _ (TyBot loc) = TyTop loc
dualType _ (TyTop loc) = TyBot loc
dualType pol (TyUnion loc mk t1 t2) = TyInter loc mk (dualType pol t1) (dualType pol t2)
dualType pol (TyInter loc mk t1 t2) = TyUnion loc mk (dualType pol t1) (dualType pol t2)
dualType pol (TyRec loc p x t) = TyRec loc (flipPolarityRep p) x (dualType pol t)
dualType pol (TySyn loc _ rn ty) = TySyn loc (flipPolarityRep pol) (dualRnTypeName rn) (dualType pol ty)
dualType PosRep (TyData loc _ xtors) = TyCodata loc NegRep  xtors
dualType NegRep (TyData loc _ xtors) = TyCodata loc PosRep  xtors
dualType PosRep (TyCodata loc _ xtors) = TyData loc NegRep  xtors
dualType NegRep (TyCodata loc _ xtors) = TyData loc PosRep  xtors
dualType PosRep (TyDataRefined loc _ rn xtors) = TyCodataRefined loc NegRep  (dualRnTypeName rn) xtors
dualType NegRep (TyDataRefined loc _ rn xtors) = TyCodataRefined loc PosRep  (dualRnTypeName rn) xtors
dualType PosRep (TyCodataRefined loc _ rn xtors) = TyDataRefined loc NegRep  (dualRnTypeName rn) xtors
dualType NegRep (TyCodataRefined loc _ rn xtors) = TyDataRefined loc PosRep  (dualRnTypeName rn) xtors
dualType _ (TyFlipPol _ ty) = ty

dualVariantType :: PolarityRep pol -> VariantType pol -> VariantType (FlipPol pol)
dualVariantType pol (CovariantType ty) = CovariantType (dualType pol ty)
dualVariantType PosRep (ContravariantType ty) = ContravariantType (dualType NegRep ty)
dualVariantType NegRep (ContravariantType ty) = ContravariantType (dualType PosRep ty)

dualRnTypeName :: RnTypeName -> RnTypeName
dualRnTypeName (MkRnTypeName _loc _doc _fp mn tn) = MkRnTypeName defaultLoc Nothing Nothing mn (dualTypeName tn)

-- >>> dualTypeName (MkTypeName "Foo")
-- MkTypeName {unTypeName = "CoFoo"}

-- >>> dualTypeName (MkTypeName "CoApp")
-- MkTypeName {unTypeName = "App"}

dualTypeName :: TypeName -> TypeName
dualTypeName (MkTypeName (T.stripPrefix "Co" -> Just n)) | T.length n > 0 = MkTypeName n
dualTypeName (MkTypeName tn) = MkTypeName $ T.pack "Co" `T.append` tn

dualMonoKind :: MonoKind -> MonoKind
dualMonoKind mk = mk

dualTypeScheme :: PolarityRep pol ->TypeScheme pol -> TypeScheme (FlipPol pol)
dualTypeScheme pol (TypeScheme _  ts_vars ty) = TypeScheme defaultLoc ts_vars (dualType pol ty)
