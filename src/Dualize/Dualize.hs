module Dualize.Dualize where

import Data.Text qualified as T
import Data.Bifunctor ( Bifunctor(bimap) )
import Data.Functor ( (<&>) )

import Syntax.CST.Kinds
import Syntax.CST.Names
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCnsRep(..), PrdCns(..))
import Syntax.RST.Terms (PrimitiveOp)
import Syntax.RST.Types (FlipPol, FlipPrdCns, PolarityRep(..), flipPolarityRep, flipPrdCns)
import Syntax.RST.Program (PrdCnsToPol)
import Syntax.TST.Types qualified as TST
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms
import Syntax.Core.Annot
import Loc

------------------------------------------------------------------------------
-- Dualization
------------------------------------------------------------------------------

data DualizeError
    = DualPrim Loc String 
    | DualPrint Loc String  
    | DualRead Loc String 
    | DualPrimOp Loc PrimitiveOp String 
    | DualMethod Loc String
  deriving Show

------------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------------

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
    return $ Apply defaultLoc (dualApplyAnnot annot) (dualMonoKind kind) t1 t2
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
dualSubst = fmap MkSubstitution . mapM dualPrdCnsTerm . unSubstitution
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

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

dualType' :: PrdCnsRep pc -> TST.Typ (PrdCnsToPol pc)  -> TST.Typ (PrdCnsToPol (FlipPrdCns pc))
dualType' PrdRep t = dualType PosRep t
dualType' CnsRep t = dualType NegRep t

dualType :: PolarityRep pol -> TST.Typ pol -> TST.Typ (FlipPol pol)
dualType pol (TST.TyUniVar _loc _ kind x) = TST.TyUniVar defaultLoc (flipPolarityRep pol) (dualMonoKind kind) x
dualType pol (TST.TySkolemVar _loc _ kind x) = TST.TySkolemVar defaultLoc (flipPolarityRep pol) (dualMonoKind kind) x
dualType pol (TST.TyRecVar _loc _ kind x) = TST.TyRecVar defaultLoc (flipPolarityRep pol) (dualMonoKind kind) x
dualType pol (TST.TyNominal _ _ kind tn vtys) = TST.TyNominal defaultLoc  (flipPolarityRep pol) (dualMonoKind kind) (dualRnTypeName tn) (dualVariantType pol <$> vtys)
dualType pol (TST.TyI64 loc _ ) = TST.TyI64 loc (flipPolarityRep pol)
dualType pol (TST.TyF64 loc _ ) = TST.TyF64 loc (flipPolarityRep pol)
dualType pol (TST.TyChar loc _ ) = TST.TyChar loc (flipPolarityRep pol)
dualType pol (TST.TyString loc _ ) = TST.TyString loc (flipPolarityRep pol)
dualType _ (TST.TyBot loc mk) = TST.TyTop loc mk
dualType _ (TST.TyTop loc mk) = TST.TyBot loc mk
dualType pol (TST.TyUnion loc mk t1 t2) = TST.TyInter loc mk (dualType pol t1) (dualType pol t2)
dualType pol (TST.TyInter loc mk t1 t2) = TST.TyUnion loc mk (dualType pol t1) (dualType pol t2)
dualType pol (TST.TyRec loc p x t) = TST.TyRec loc (flipPolarityRep p) x (dualType pol t)
dualType pol (TST.TySyn loc _ rn ty) = TST.TySyn loc (flipPolarityRep pol) (dualRnTypeName rn) (dualType pol ty)
dualType PosRep (TST.TyData loc _ mk xtors) = TST.TyCodata loc NegRep (dualMonoKind mk) xtors 
dualType NegRep (TST.TyData loc _ mk xtors) = TST.TyCodata loc PosRep (dualMonoKind mk) xtors 
dualType PosRep (TST.TyCodata loc _ mk xtors) = TST.TyData loc NegRep  (dualMonoKind mk) xtors
dualType NegRep (TST.TyCodata loc _ mk xtors) = TST.TyData loc PosRep  (dualMonoKind mk) xtors 
dualType PosRep (TST.TyDataRefined loc _ mk rn xtors) = TST.TyCodataRefined loc NegRep  (dualMonoKind mk) (dualRnTypeName rn) xtors
dualType NegRep (TST.TyDataRefined loc _ mk rn xtors) = TST.TyCodataRefined loc PosRep  mk(dualRnTypeName rn) xtors
dualType PosRep (TST.TyCodataRefined loc _ mk rn xtors) = TST.TyDataRefined loc NegRep  (dualMonoKind mk) (dualRnTypeName rn) xtors
dualType NegRep (TST.TyCodataRefined loc _ mk rn xtors) = TST.TyDataRefined loc PosRep  (dualMonoKind mk) (dualRnTypeName rn) xtors
dualType _ (TST.TyFlipPol _ ty) = ty

dualVariantType :: PolarityRep pol -> TST.VariantType pol -> TST.VariantType (FlipPol pol)
dualVariantType pol (TST.CovariantType ty) = TST.CovariantType (dualType pol ty)
dualVariantType PosRep (TST.ContravariantType ty) = TST.ContravariantType (dualType NegRep ty)
dualVariantType NegRep (TST.ContravariantType ty) = TST.ContravariantType (dualType PosRep ty)

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

dualTypeScheme :: PolarityRep pol -> TST.TypeScheme pol -> TST.TypeScheme (FlipPol pol)
dualTypeScheme pol (TST.TypeScheme _  ts_vars ty) = TST.TypeScheme defaultLoc ts_vars (dualType pol ty)


flipDC :: CST.DataCodata -> CST.DataCodata
flipDC CST.Data = CST.Codata 
flipDC CST.Codata = CST.Data 

dualPolyKind :: PolyKind -> PolyKind 
dualPolyKind pk = pk 

dualDataDecl :: TST.DataDecl -> TST.DataDecl
dualDataDecl TST.NominalDecl { data_loc, data_doc, data_name, data_polarity, data_kind, data_xtors = (sigsPos,sigsNeg) } =
    TST.NominalDecl { data_loc = data_loc
                    , data_doc = data_doc
                    , data_name = dualRnTypeName data_name
                    , data_polarity = flipDC data_polarity
                    , data_kind = dualPolyKind data_kind
                    , data_xtors = (dualXtorSig PosRep <$> sigsPos,dualXtorSig NegRep <$> sigsNeg )
                    }
dualDataDecl TST.RefinementDecl { data_loc
                                , data_doc
                                , data_name
                                , data_polarity
                               , data_refinement_empty = (refinementEmptyPos, refinementEmptyNeg)
                               , data_refinement_full = (refinementFullPos, refinementFullNeg)
                                , data_kind
                                , data_xtors = (sigsPos,sigsNeg)
                                , data_xtors_refined = (sigsPosRefined, sigsNegRefined) } = do
    TST.RefinementDecl { data_loc = data_loc
                       , data_doc = data_doc
                       , data_name = dualRnTypeName data_name
                       , data_polarity = flipDC data_polarity
                       , data_refinement_empty = ( dualType NegRep refinementEmptyNeg
                                                 , dualType PosRep refinementEmptyPos)
                       , data_refinement_full = ( dualType NegRep refinementFullNeg
                                                , dualType PosRep refinementFullPos)
                       , data_kind = dualPolyKind data_kind
                       , data_xtors = (dualXtorSig PosRep <$> sigsPos,dualXtorSig NegRep <$> sigsNeg)
                       , data_xtors_refined = (dualXtorSig PosRep <$> sigsPosRefined,dualXtorSig NegRep <$> sigsNegRefined )
                     }

dualXtorSig ::  PolarityRep pol ->TST.XtorSig pol -> TST.XtorSig pol
dualXtorSig pol (TST.MkXtorSig xtor lctx) = TST.MkXtorSig (dualXtorName xtor) (dualPrdCnsType pol <$> lctx)


dualPrdCnsType :: PolarityRep pol -> TST.PrdCnsType pol -> TST.PrdCnsType pol
dualPrdCnsType PosRep (TST.PrdCnsType PrdRep ty) = TST.PrdCnsType CnsRep (TST.TyFlipPol NegRep ty)
dualPrdCnsType NegRep (TST.PrdCnsType PrdRep ty) = TST.PrdCnsType CnsRep (TST.TyFlipPol PosRep ty)
dualPrdCnsType PosRep (TST.PrdCnsType CnsRep ty) = TST.PrdCnsType PrdRep (TST.TyFlipPol PosRep ty)
dualPrdCnsType NegRep (TST.PrdCnsType CnsRep ty) = TST.PrdCnsType PrdRep (TST.TyFlipPol NegRep ty)

