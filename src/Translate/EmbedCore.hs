module Translate.EmbedCore () where

import Syntax.CST.Types (PrdCnsRep(..))
import Syntax.RST.Program qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Program qualified as Core
import Sugar.Core qualified as Core

import Translate.Reparse (Embed (..))

instance Embed Core.CmdCase RST.CmdCase where
  embed :: Core.CmdCase -> RST.CmdCase
  embed Core.MkCmdCase {cmdcase_loc, cmdcase_pat, cmdcase_cmd } =
      RST.MkCmdCase { cmdcase_loc = cmdcase_loc
                    , cmdcase_pat = cmdcase_pat
                    , cmdcase_cmd = embed cmdcase_cmd
                    }

instance Embed Core.InstanceCase RST.InstanceCase where
  embed :: Core.InstanceCase -> RST.InstanceCase
  embed Core.MkInstanceCase {instancecase_loc, instancecase_pat, instancecase_cmd } =
      RST.MkInstanceCase { instancecase_loc = instancecase_loc
                        , instancecase_pat = instancecase_pat
                        , instancecase_cmd = embed instancecase_cmd
                        }

instance Embed Core.PrdCnsTerm RST.PrdCnsTerm where
  embed :: Core.PrdCnsTerm -> RST.PrdCnsTerm
  embed (Core.PrdTerm tm) = RST.PrdTerm (embed tm)
  embed (Core.CnsTerm tm) = RST.CnsTerm (embed tm)

instance Embed Core.Substitution RST.Substitution where
  embed :: Core.Substitution -> RST.Substitution
  embed = fmap embed

instance Embed (Core.Term pc) (RST.Term pc) where
  embed :: Core.Term pc -> RST.Term pc
  embed (Core.BoundVar loc rep idx) =
      RST.BoundVar loc rep idx
  embed (Core.FreeVar loc rep idx) =
      RST.FreeVar loc rep idx
  embed (Core.RawXtor loc rep ns xs subst) =
      RST.Xtor loc rep ns xs (embed subst)
  embed (Core.RawCase loc rep ns cases) =
      RST.XCase loc rep ns (embed <$> cases)
  embed (Core.RawMuAbs loc rep b cmd) =
      RST.MuAbs loc rep b (embed cmd)
  embed (Core.CocaseOf loc rep ns t cases) =
      RST.CocaseOf loc rep ns (embed t) (embed <$> cases)
  embed (Core.CaseOf loc rep ns t cases) = RST.CaseOf loc rep ns (embed t) (embed <$> cases)
  embed (Core.Dtor loc rep ns xt t (subst,r,subst2)) = RST.Dtor loc rep ns xt (embed t) (embed subst, r, embed subst2)
  embed (Core.Semi loc rep ns xt (subst,r,subst2) t ) = RST.Semi loc rep ns xt (embed subst, r, embed subst2) (embed t)
  embed (Core.XCaseI loc rep PrdRep ns cases) = RST.CocaseI loc rep ns (embed <$> cases)
  embed (Core.XCaseI loc rep CnsRep ns cases) = RST.CaseI loc rep ns (embed <$> cases)
  embed (Core.Lambda loc rep fv tm)  = RST.Lambda loc rep fv (embed tm)
  embed (Core.XCase loc _ pc ns cases) = RST.XCase loc pc ns (embed <$> cases) -- revisit
  embed (Core.PrimLitI64 loc d) =
      RST.PrimLitI64 loc d
  embed (Core.PrimLitF64 loc d) =
      RST.PrimLitF64 loc d
  embed (Core.PrimLitChar loc d) =
      RST.PrimLitChar loc d
  embed (Core.PrimLitString loc d) =
      RST.PrimLitString loc d

instance Embed (Core.TermCase pc) (RST.TermCase pc) where
  embed :: Core.TermCase pc -> RST.TermCase pc
  embed (Core.MkTermCase loc pat t) = RST.MkTermCase loc pat (embed t)

instance Embed (Core.TermCaseI pc) (RST.TermCaseI pc) where
  embed :: Core.TermCaseI pc -> RST.TermCaseI pc
  embed (Core.MkTermCaseI loc pati t) = RST.MkTermCaseI loc pati (embed t)

instance Embed Core.Command RST.Command where
  embed :: Core.Command -> RST.Command
  embed (Core.RawApply loc prd cns ) =
      RST.Apply loc (embed prd) (embed cns)
  embed (Core.CocaseOfI loc rep ns t cases) =
      RST.CocaseOfI loc rep ns (embed t) (embed <$> cases)
  embed (Core.CaseOfI loc rep ns t cases) =
      RST.CaseOfI loc rep ns  (embed t) (embed <$> cases)
  embed (Core.CocaseOfCmd loc ns t cases) = RST.CocaseOfCmd loc ns (embed t) (embed <$> cases)
  embed (Core.CaseOfCmd loc ns t cases) = RST.CaseOfCmd loc ns (embed t) (embed <$> cases)
  embed (Core.Method loc mn cn subst) = RST.Method loc mn cn (embed subst)
  embed (Core.Print loc tm cmd) =
      RST.Print loc (embed tm) (embed cmd)
  embed (Core.Read loc tm) =
      RST.Read loc (embed tm)
  embed (Core.Jump loc fv) =
      RST.Jump loc fv
  embed (Core.ExitSuccess loc) =
      RST.ExitSuccess loc
  embed (Core.ExitFailure loc) =
      RST.ExitFailure loc
  embed (Core.PrimOp loc op subst) =
      RST.PrimOp loc op (embed subst)


instance Embed Core.Module RST.Module where
  embed :: Core.Module -> RST.Module
  embed Core.MkModule { mod_name, mod_fp, mod_decls } =
      RST.MkModule { mod_name = mod_name
                  , mod_fp = mod_fp
                  , mod_decls = embed <$> mod_decls
                  }

instance Embed (Core.PrdCnsDeclaration pc) (RST.PrdCnsDeclaration pc) where
  embed :: Core.PrdCnsDeclaration pc -> RST.PrdCnsDeclaration pc
  embed Core.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term } =
      RST.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                              , pcdecl_doc = pcdecl_doc
                              , pcdecl_pc = pcdecl_pc
                              , pcdecl_isRec = pcdecl_isRec
                              , pcdecl_name = pcdecl_name
                              , pcdecl_annot = pcdecl_annot
                              , pcdecl_term = embed pcdecl_term
                              }

instance Embed Core.CommandDeclaration RST.CommandDeclaration where
  embed :: Core.CommandDeclaration -> RST.CommandDeclaration
  embed Core.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
      RST.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                              , cmddecl_doc = cmddecl_doc
                              , cmddecl_name = cmddecl_name
                              , cmddecl_cmd = embed cmddecl_cmd
                              }

instance Embed Core.InstanceDeclaration RST.InstanceDeclaration where
  embed :: Core.InstanceDeclaration -> RST.InstanceDeclaration
  embed Core.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases } =
      RST.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                                , instancedecl_doc = instancedecl_doc
                                , instancedecl_name = instancedecl_name
                                , instancedecl_typ = instancedecl_typ
                                , instancedecl_cases = embed <$> instancedecl_cases
                                }

instance Embed Core.Declaration RST.Declaration where
  embed :: Core.Declaration -> RST.Declaration
  embed (Core.PrdCnsDecl pcrep decl) =
      RST.PrdCnsDecl pcrep (embed decl)
  embed (Core.CmdDecl decl) =
      RST.CmdDecl (embed decl)
  embed (Core.DataDecl decl) =
      RST.DataDecl decl
  embed (Core.XtorDecl decl) =
      RST.XtorDecl decl
  embed (Core.ImportDecl decl) =
      RST.ImportDecl decl
  embed (Core.SetDecl decl) =
      RST.SetDecl decl
  embed (Core.TyOpDecl decl) =
      RST.TyOpDecl decl
  embed (Core.TySynDecl decl) =
      RST.TySynDecl decl
  embed (Core.ClassDecl decl) =
      RST.ClassDecl decl
  embed (Core.InstanceDecl decl) =
      RST.InstanceDecl (embed decl)

