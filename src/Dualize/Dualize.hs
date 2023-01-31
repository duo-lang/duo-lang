module Dualize.Dualize (dualDataDecl, dualPrdCnsDeclaration, dualCmdDeclaration) where

import Data.Text qualified as T -- implementation of unicode text, qualified as T to avoid name clashes with prelude
import Data.Text (Text)
import Data.Bifunctor ( Bifunctor(bimap) )
import Data.Functor ( (<&>) )

-- import the needed parts of the syntax trees
import Syntax.CST.Kinds
import Syntax.CST.Names
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCnsRep(..), PrdCns(..))
import Syntax.RST.Terms (PrimitiveOp)
import Syntax.RST.Types (FlipPol, FlipPrdCns, PolarityRep(..), flipPolarityRep, flipPrdCns)
import Syntax.RST.Program (PrdCnsToPol)
import Syntax.Core.Terms (Pattern(..))
import Syntax.TST.Types qualified as TST
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms
import Syntax.Core.Annot
import Loc -- source code locations, see src/Loc.hs

------------------------------------------------------------------------------
-- Dualization
------------------------------------------------------------------------------

-- Datatype DualizeError
-- returned if dualization is not possible

data DualizeError
 = DualPrim Loc Text
 | DualPrint Loc Text
 | DualRead Loc Text
 | DualPrimOp Loc PrimitiveOp Text
 | DualMethod Loc Text
 | DualNotAnnotated Loc
 deriving Show

-- PrdCns is the Datatype that includes Prd and Cns
flipPC :: PrdCns -> PrdCns
flipPC Prd = Cns
flipPC Cns = Prd

-- uses the DataCodata Datatype from CST
flipDC :: CST.DataCodata -> CST.DataCodata
flipDC CST.Data = CST.Codata 
flipDC CST.Codata = CST.Data 

type DualizeM a = Either DualizeError a

throwDualizeError :: forall a. DualizeError -> DualizeM a
throwDualizeError = Left

------------------------------------------------------------------------------
-- Names
------------------------------------------------------------------------------

-- prepend "Co" to Xtor names
dualXtorName :: XtorName -> XtorName
dualXtorName (MkXtorName (T.stripPrefix "Co" -> Just n)) | T.length n > 0 = MkXtorName n
dualXtorName (MkXtorName x) = MkXtorName (T.pack "Co" `T.append` x)

-- prepend "Co" to free variable names
dualFVName :: FreeVarName -> FreeVarName
dualFVName (MkFreeVarName (T.stripPrefix "co" -> Just n)) | T.length n > 0 = MkFreeVarName n
dualFVName (MkFreeVarName x) = MkFreeVarName (T.pack "co" `T.append` x)

-- prepend "Co" to type names
dualTypeName :: TypeName -> TypeName
dualTypeName (MkTypeName (T.stripPrefix "Co" -> Just n)) | T.length n > 0 = MkTypeName n
dualTypeName (MkTypeName tn) = MkTypeName $ T.pack "Co" `T.append` tn

-- 
dualRnTypeName :: RnTypeName -> RnTypeName
dualRnTypeName (MkRnTypeName _loc _doc _fp mn tn) =
  MkRnTypeName defaultLoc Nothing Nothing mn (dualTypeName tn)

------------------------------------------------------------------------------
-- Terms
------------------------------------------------------------------------------

dualTerm :: Term pc -> DualizeM (Term (FlipPrdCns pc))
dualTerm (BoundVar _ rep ty i) =
  pure $ BoundVar defaultLoc (flipPrdCns rep) (dualType' rep ty) i
dualTerm (FreeVar _ rep ty i) =
  pure $ FreeVar defaultLoc (flipPrdCns rep) (dualType' rep ty) (dualFVName i)
dualTerm (Xtor _ annot rep ty ns xtor subst) = do
  subst' <- dualSubst subst
  pure $ Xtor defaultLoc (dualXtorAnnot annot) (flipPrdCns rep) (dualType' rep ty) ns (dualXtorName xtor) subst'
dualTerm (XCase _ annot rep ty ns cases) = do
  cases' <- mapM dualCmdCase cases
  pure $ XCase defaultLoc (dualMatchAnnot annot) (flipPrdCns rep) (dualType' rep ty) ns cases'
dualTerm (MuAbs _ annot rep ty fv cmd) = do
  cmd' <- dualCmd cmd
  pure $ MuAbs defaultLoc (dualMuAnnot annot)  (flipPrdCns rep)  (dualType' rep ty) (dualFVName <$> fv) cmd'
dualTerm (PrimLitI64 loc i) =
  throwDualizeError (DualPrim loc $ "Cannot dualize integer literal: " <> T.pack (show i))
dualTerm (PrimLitF64 loc i) =
  throwDualizeError (DualPrim loc $ "Cannot dualize floating point literal: " <> T.pack (show i))
dualTerm (PrimLitChar loc i) =
  throwDualizeError (DualPrim loc $ "Cannot dualize character literal: " <> T.pack (show i))
dualTerm (PrimLitString loc i) =
  throwDualizeError (DualPrim loc $ "Cannot dualize string literal: " <> T.pack (show i))

dualCmd :: Command -> DualizeM Command
dualCmd (Apply _ annot kind prd cns) = do
  t1 <- dualTerm cns
  t2 <- dualTerm prd
  pure $ Apply defaultLoc (dualApplyAnnot annot) (dualMonoKind kind) t1 t2
dualCmd (Print loc _ _) =
  throwDualizeError (DualPrint loc "Cannot dualize Print command")
dualCmd (Read loc _)  =
  throwDualizeError (DualRead loc "Cannot dualize Read command")
dualCmd (Jump _ fv)  =
  pure $ Jump defaultLoc (dualFVName fv)
dualCmd (Method loc _ _ _ _ _) =
  throwDualizeError (DualMethod loc "Cannot dualize type class method")
dualCmd (PrimOp loc op _) =
  throwDualizeError(DualPrimOp loc op "Cannot dualize primitive op")
dualCmd (ExitSuccess _) =
  pure $ ExitSuccess defaultLoc
dualCmd (ExitFailure _) =
  pure $ ExitFailure defaultLoc

dualCmdCase :: CmdCase -> DualizeM CmdCase
dualCmdCase (MkCmdCase _ pat cmd) = do
  cmd' <- dualCmd cmd
  pure $ MkCmdCase defaultLoc (dualPattern pat) cmd'

dualPattern :: Pattern -> Pattern
dualPattern (XtorPat _ xtor vars) =
  XtorPat defaultLoc (dualXtorName xtor) (map (bimap flipPC (dualFVName <$>)) vars)

dualSubst :: Substitution -> DualizeM Substitution
dualSubst = fmap MkSubstitution . mapM dualPrdCnsTerm . unSubstitution

dualPrdCnsTerm :: PrdCnsTerm -> DualizeM PrdCnsTerm
dualPrdCnsTerm (PrdTerm t) = dualTerm t <&> CnsTerm
dualPrdCnsTerm (CnsTerm t) = dualTerm t <&> PrdTerm

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

------------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------------

dualMonoKind :: MonoKind -> MonoKind
dualMonoKind mk = mk

dualPolyKind :: PolyKind -> PolyKind 
dualPolyKind pk = pk 

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

dualType' :: PrdCnsRep pc -> TST.Typ (PrdCnsToPol pc)  -> TST.Typ (PrdCnsToPol (FlipPrdCns pc))
dualType' PrdRep t = dualType PosRep t
dualType' CnsRep t = dualType NegRep t

dualType :: PolarityRep pol -> TST.Typ pol -> TST.Typ (FlipPol pol)
dualType pol (TST.TyUniVar _loc _ kind x) =
  TST.TyUniVar defaultLoc (flipPolarityRep pol) (dualMonoKind kind) x
dualType pol (TST.TySkolemVar _loc _ kind x) =
  TST.TySkolemVar defaultLoc (flipPolarityRep pol) (dualMonoKind kind) x
dualType pol (TST.TyRecVar _loc _ kind x) =
  TST.TyRecVar defaultLoc (flipPolarityRep pol) (dualMonoKind kind) x
dualType pol (TST.TyNominal _ _ kind tn) =
  TST.TyNominal defaultLoc  (flipPolarityRep pol) (dualPolyKind kind) (dualRnTypeName tn)
dualType pol (TST.TyApp _ _ ty args) = 
  TST.TyApp defaultLoc (flipPolarityRep pol) (dualType pol ty) (dualVariantType pol <$> args)
dualType pol (TST.TyI64 loc _ ) =
  TST.TyI64 loc (flipPolarityRep pol)
dualType pol (TST.TyF64 loc _ ) =
  TST.TyF64 loc (flipPolarityRep pol)
dualType pol (TST.TyChar loc _ ) =
  TST.TyChar loc (flipPolarityRep pol)
dualType pol (TST.TyString loc _ ) =
  TST.TyString loc (flipPolarityRep pol)
dualType _ (TST.TyBot loc mk) =
  TST.TyTop loc mk
dualType _ (TST.TyTop loc mk) = TST.TyBot loc mk
dualType pol (TST.TyUnion loc mk t1 t2) =
  TST.TyInter loc mk (dualType pol t1) (dualType pol t2)
dualType pol (TST.TyInter loc mk t1 t2) =
  TST.TyUnion loc mk (dualType pol t1) (dualType pol t2)
dualType pol (TST.TyRec loc p x t) =
  TST.TyRec loc (flipPolarityRep p) x (dualType pol t)
dualType pol (TST.TySyn loc _ rn ty) =
  TST.TySyn loc (flipPolarityRep pol) (dualRnTypeName rn) (dualType pol ty)
dualType PosRep (TST.TyData loc _ mk xtors) =
  TST.TyCodata loc NegRep (dualMonoKind mk) xtors 
dualType NegRep (TST.TyData loc _ mk xtors) =
  TST.TyCodata loc PosRep (dualMonoKind mk) xtors 
dualType PosRep (TST.TyCodata loc _ mk xtors) =
  TST.TyData loc NegRep  (dualMonoKind mk) xtors
dualType NegRep (TST.TyCodata loc _ mk xtors) =
  TST.TyData loc PosRep  (dualMonoKind mk) xtors 
dualType PosRep (TST.TyDataRefined loc _ mk rn xtors) =
  TST.TyCodataRefined loc NegRep  (dualMonoKind mk) (dualRnTypeName rn) xtors
dualType NegRep (TST.TyDataRefined loc _ mk rn xtors) =
  TST.TyCodataRefined loc PosRep  mk(dualRnTypeName rn) xtors
dualType PosRep (TST.TyCodataRefined loc _ mk rn xtors) =
  TST.TyDataRefined loc NegRep  (dualMonoKind mk) (dualRnTypeName rn) xtors
dualType NegRep (TST.TyCodataRefined loc _ mk rn xtors) =
  TST.TyDataRefined loc PosRep  (dualMonoKind mk) (dualRnTypeName rn) xtors
dualType _ (TST.TyFlipPol _ ty) = ty

dualVariantType :: PolarityRep pol -> TST.VariantType pol -> TST.VariantType (FlipPol pol)
dualVariantType pol (TST.CovariantType ty) =
  TST.CovariantType (dualType pol ty)
dualVariantType PosRep (TST.ContravariantType ty) =
  TST.ContravariantType (dualType NegRep ty)
dualVariantType NegRep (TST.ContravariantType ty) =
  TST.ContravariantType (dualType PosRep ty)

dualTypeScheme :: PolarityRep pol -> TST.TypeScheme pol -> TST.TypeScheme (FlipPol pol)
dualTypeScheme pol (TST.TypeScheme _  ts_vars ty) = TST.TypeScheme defaultLoc ts_vars (dualType pol ty)

------------------------------------------------------------------------------
-- Declarations
------------------------------------------------------------------------------

dualPrdCnsDeclaration :: TST.PrdCnsDeclaration pc -> DualizeM (TST.PrdCnsDeclaration (FlipPrdCns pc))
dualPrdCnsDeclaration (TST.MkPrdCnsDeclaration loc doc rep isrec fv (TST.Annotated tys) tm) = do
  tm' <- dualTerm tm
  case rep of
    PrdRep -> pure (TST.MkPrdCnsDeclaration loc doc CnsRep isrec (dualFVName fv) (TST.Annotated (dualTypeScheme PosRep tys)) tm')
    CnsRep -> pure (TST.MkPrdCnsDeclaration loc doc PrdRep isrec (dualFVName fv) (TST.Annotated (dualTypeScheme NegRep tys)) tm')
dualPrdCnsDeclaration (TST.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_annot = TST.Inferred _ }) =
  throwDualizeError (DualNotAnnotated pcdecl_loc)

dualCmdDeclaration :: TST.CommandDeclaration -> DualizeM TST.CommandDeclaration
dualCmdDeclaration (TST.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd }) = do
  cmd' <- dualCmd cmddecl_cmd
  pure TST.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                                , cmddecl_doc = cmddecl_doc
                                , cmddecl_name = dualFVName cmddecl_name
                                , cmddecl_cmd = cmd'
                                }

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
