module Translate.EmbedTST () where

import Translate.EmbedRST (Embed(..))
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Types qualified as TST
import Syntax.RST.Types qualified as RST
import qualified Data.Bifunctor as BF (bimap)
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Program qualified as Core

instance Embed TST.CmdCase Core.CmdCase where
  embed :: TST.CmdCase -> Core.CmdCase
  embed TST.MkCmdCase {cmdcase_loc, cmdcase_pat, cmdcase_cmd } =
      Core.MkCmdCase { cmdcase_loc = cmdcase_loc
                    , cmdcase_pat = cmdcase_pat
                    , cmdcase_cmd = embed cmdcase_cmd
                    }

instance Embed TST.InstanceCase Core.InstanceCase where
  embed :: TST.InstanceCase -> Core.InstanceCase
  embed TST.MkInstanceCase {instancecase_loc, instancecase_pat, instancecase_cmd } =
      Core.MkInstanceCase { instancecase_loc = instancecase_loc
                          , instancecase_pat = instancecase_pat
                          , instancecase_cmd = embed instancecase_cmd
                          }

instance Embed TST.PrdCnsTerm Core.PrdCnsTerm where
  embed :: TST.PrdCnsTerm -> Core.PrdCnsTerm
  embed (TST.PrdTerm tm) = Core.PrdTerm (embed tm)
  embed (TST.CnsTerm tm) = Core.CnsTerm (embed tm)


instance Embed TST.Substitution Core.Substitution where
  embed :: TST.Substitution -> Core.Substitution
  embed = fmap embed

instance Embed (TST.Term pc) (Core.Term pc) where
  embed :: TST.Term pc -> Core.Term pc
  embed (TST.BoundVar loc rep _ty idx) =
      Core.BoundVar loc rep idx
  embed (TST.FreeVar loc rep _ty idx) =
      Core.FreeVar loc rep idx
  embed (TST.Xtor loc annot rep _ty ns xs subst) =
      Core.Xtor loc annot rep ns xs (embed subst)
  embed (TST.XCase loc annot rep _ty ns cases) =
      Core.XCase loc annot rep ns (embed <$> cases)
  embed (TST.MuAbs loc annot rep _ty b cmd) =
      Core.MuAbs loc annot rep b (embed cmd)
  embed (TST.PrimLitI64 loc i) =
      Core.PrimLitI64 loc i
  embed (TST.PrimLitF64 loc d) =
      Core.PrimLitF64 loc d
  embed (TST.PrimLitChar loc d) =
      Core.PrimLitChar loc d
  embed (TST.PrimLitString loc d) =
      Core.PrimLitString loc d


instance Embed TST.Command Core.Command where
  embed :: TST.Command -> Core.Command
  embed (TST.Apply loc annot _kind prd cns ) =
      Core.Apply loc annot (embed prd) (embed cns)
  embed (TST.Print loc tm cmd) =
      Core.Print loc (embed tm) (embed cmd)
  embed (TST.Read loc tm) =
      Core.Read loc (embed tm)
  embed (TST.Jump loc fv) =
      Core.Jump loc fv
  embed (TST.Method loc mn cn subst) =
      Core.Method loc mn cn (embed subst)
  embed (TST.ExitSuccess loc) =
      Core.ExitSuccess loc
  embed (TST.ExitFailure loc) =
      Core.ExitFailure loc
  embed (TST.PrimOp loc op subst) =
      Core.PrimOp loc op (embed subst)

instance Embed TST.Module Core.Module where
  embed :: TST.Module -> Core.Module
  embed TST.MkModule { mod_name, mod_fp, mod_decls } =
      Core.MkModule { mod_name = mod_name
                    , mod_fp = mod_fp
                    , mod_decls = embed <$> mod_decls
                    }

instance Embed (TST.PrdCnsDeclaration pc) (Core.PrdCnsDeclaration pc) where
  embed :: TST.PrdCnsDeclaration pc -> Core.PrdCnsDeclaration pc
  embed TST.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot = TST.Annotated tys, pcdecl_term } =
      Core.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                              , pcdecl_doc = pcdecl_doc
                              , pcdecl_pc = pcdecl_pc
                              , pcdecl_isRec = pcdecl_isRec
                              , pcdecl_name = pcdecl_name
                              , pcdecl_annot = Just (embed tys)
                              , pcdecl_term = embed pcdecl_term
                              }
  embed TST.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot = TST.Inferred _, pcdecl_term } =
      Core.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                              , pcdecl_doc = pcdecl_doc
                              , pcdecl_pc = pcdecl_pc
                              , pcdecl_isRec = pcdecl_isRec
                              , pcdecl_name = pcdecl_name
                              , pcdecl_annot = Nothing
                              , pcdecl_term = embed pcdecl_term
                              }

instance Embed TST.CommandDeclaration Core.CommandDeclaration where
  embed :: TST.CommandDeclaration -> Core.CommandDeclaration
  embed TST.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
      Core.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                                , cmddecl_doc = cmddecl_doc
                                , cmddecl_name = cmddecl_name
                                , cmddecl_cmd = embed cmddecl_cmd
                                }

instance Embed TST.InstanceDeclaration Core.InstanceDeclaration where
  embed :: TST.InstanceDeclaration -> Core.InstanceDeclaration
  embed TST.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases } =
      Core.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                                , instancedecl_doc = instancedecl_doc
                                , instancedecl_name = instancedecl_name
                                , instancedecl_typ = BF.bimap embed embed instancedecl_typ
                                , instancedecl_cases = embed <$> instancedecl_cases
                                }


instance Embed TST.Declaration Core.Declaration where
  embed :: TST.Declaration -> Core.Declaration
  embed (TST.PrdCnsDecl pcrep decl) =
      Core.PrdCnsDecl pcrep (embed decl)
  embed (TST.CmdDecl decl) =
      Core.CmdDecl (embed decl)
  embed (TST.DataDecl decl) =
      Core.DataDecl decl
  embed (TST.XtorDecl decl) =
      Core.XtorDecl decl
  embed (TST.ImportDecl decl) =
      Core.ImportDecl decl
  embed (TST.SetDecl decl) =
      Core.SetDecl decl
  embed (TST.TyOpDecl decl) =
      Core.TyOpDecl decl
  embed (TST.TySynDecl decl) =
      Core.TySynDecl decl
  embed (TST.ClassDecl decl) =
      Core.ClassDecl decl
  embed (TST.InstanceDecl decl) =
      Core.InstanceDecl (embed decl)


instance Embed (TST.PrdCnsType pol) (RST.PrdCnsType pol) where
  embed :: TST.PrdCnsType pol -> RST.PrdCnsType pol
  embed (TST.PrdCnsType pc tp) = RST.PrdCnsType pc (embed tp)

instance Embed (TST.XtorSig pol) (RST.XtorSig pol) where
  embed :: TST.XtorSig pol -> RST.XtorSig pol
  embed TST.MkXtorSig {sig_name = name, sig_args = cont} = RST.MkXtorSig {sig_name=name, sig_args = map embed cont}

instance Embed (TST.VariantType pol) (RST.VariantType pol) where
  embed :: TST.VariantType pol -> RST.VariantType pol
  embed (TST.CovariantType tp) = RST.CovariantType (embed tp)
  embed (TST.ContravariantType tp) = RST.ContravariantType (embed tp)

instance Embed (TST.TypeScheme pol) (RST.TypeScheme pol) where
  embed :: TST.TypeScheme pol -> RST.TypeScheme pol
  embed TST.TypeScheme {ts_loc = loc, ts_vars = tyvars, ts_monotype = mt} = RST.TypeScheme {ts_loc = loc, ts_vars = tyvars, ts_monotype = embed mt}

instance Embed (TST.LinearContext pol) (RST.LinearContext pol) where
  embed :: TST.LinearContext pol-> RST.LinearContext pol
  embed  = map embed

instance Embed (TST.Typ pol) (RST.Typ pol) where
  embed :: TST.Typ pol -> RST.Typ pol
  embed (TST.TySkolemVar loc pol _ tv) = RST.TySkolemVar loc pol tv
  embed (TST.TyUniVar loc pol _ tv) = RST.TyUniVar loc pol tv
  embed (TST.TyRecVar loc pol _ tv) = RST.TyRecVar loc pol tv
  embed (TST.TyData loc pol _ xtors) = RST.TyData loc pol (map embed xtors)
  embed (TST.TyCodata loc pol _ xtors) = RST.TyCodata loc pol (map embed xtors)
  embed (TST.TyDataRefined loc pol _ tn xtors) = RST.TyDataRefined loc pol tn (map embed xtors)
  embed (TST.TyCodataRefined loc pol _ tn xtors) = RST.TyCodataRefined loc pol tn (map embed xtors)
  embed (TST.TyNominal loc pol _ tn varty) = RST.TyNominal loc pol tn (map embed varty)
  embed (TST.TySyn loc pol tn tp) = RST.TySyn loc pol tn (embed tp)
  embed (TST.TyBot loc _ ) = RST.TyBot loc
  embed (TST.TyTop loc _ ) = RST.TyTop loc
  embed (TST.TyUnion loc _ tp1 tp2) = RST.TyUnion loc (embed tp1) (embed tp2)
  embed (TST.TyInter loc _ tn1 tn2) = RST.TyInter loc (embed tn1) (embed tn2)
  embed (TST.TyRec loc pol rv tp) = RST.TyRec loc pol rv (embed tp)
  embed (TST.TyI64 loc pol) = RST.TyI64 loc pol
  embed (TST.TyF64 loc pol) = RST.TyF64 loc pol
  embed (TST.TyChar loc pol) = RST.TyChar loc pol
  embed (TST.TyString loc pol) = RST.TyString loc pol
  embed (TST.TyFlipPol pol tp) = RST.TyFlipPol pol (embed tp)

