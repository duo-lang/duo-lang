module Translate.EmbedCore
  ( EmbedCore(..)
  ) where

import Syntax.CST.Types (PrdCnsRep(..))
import Syntax.RST.Program qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Program qualified as Core
import Sugar.Core qualified as Core

---------------------------------------------------------------------------------
-- A typeclass for embedding Core.X into RST.X
---------------------------------------------------------------------------------

class EmbedCore a b | a -> b where
  embedCore :: a -> b

---------------------------------------------------------------------------------
-- EmbedCore implementation for terms
---------------------------------------------------------------------------------

instance EmbedCore Core.CmdCase RST.CmdCase where
  embedCore :: Core.CmdCase -> RST.CmdCase
  embedCore Core.MkCmdCase {cmdcase_loc, cmdcase_pat, cmdcase_cmd } =
      RST.MkCmdCase { cmdcase_loc = cmdcase_loc
                    , cmdcase_pat = cmdcase_pat
                    , cmdcase_cmd = embedCore cmdcase_cmd
                    }

instance EmbedCore Core.InstanceCase RST.InstanceCase where
  embedCore :: Core.InstanceCase -> RST.InstanceCase
  embedCore Core.MkInstanceCase {instancecase_loc, instancecase_pat, instancecase_cmd } =
      RST.MkInstanceCase { instancecase_loc = instancecase_loc
                         , instancecase_pat = instancecase_pat
                         , instancecase_cmd = embedCore instancecase_cmd
                         }

instance EmbedCore Core.PrdCnsTerm RST.PrdCnsTerm where
  embedCore :: Core.PrdCnsTerm -> RST.PrdCnsTerm
  embedCore (Core.PrdTerm tm) = RST.PrdTerm (embedCore tm)
  embedCore (Core.CnsTerm tm) = RST.CnsTerm (embedCore tm)

instance EmbedCore Core.Substitution RST.Substitution where
  embedCore :: Core.Substitution -> RST.Substitution
  embedCore = fmap embedCore

instance EmbedCore (Core.Term pc) (RST.Term pc) where
  embedCore :: Core.Term pc -> RST.Term pc
  embedCore (Core.BoundVar loc rep idx) =
      RST.BoundVar loc rep idx
  embedCore (Core.FreeVar loc rep idx) =
      RST.FreeVar loc rep idx
  embedCore (Core.RawXtor loc rep ns xs subst) =
      RST.Xtor loc rep ns xs (embedCore subst)
  embedCore (Core.RawCase loc rep ns cases) =
      RST.XCase loc rep ns (embedCore <$> cases)
  embedCore (Core.RawMuAbs loc rep b cmd) =
      RST.MuAbs loc rep b (embedCore cmd)
  embedCore (Core.CocaseOf loc rep ns t cases) =
      RST.CocaseOf loc rep ns (embedCore t) (embedCore <$> cases)
  embedCore (Core.CaseOf loc rep ns t cases) =
    RST.CaseOf loc rep ns (embedCore t) (embedCore <$> cases)
  embedCore (Core.Dtor loc rep ns xt t (subst,r,subst2)) =
    RST.Dtor loc rep ns xt (embedCore t) (embedCore subst, r, embedCore subst2)
  embedCore (Core.Semi loc rep ns xt (subst,r,subst2) t ) =
    RST.Semi loc rep ns xt (embedCore subst, r, embedCore subst2) (embedCore t)
  embedCore (Core.XCaseI loc rep PrdRep ns cases) =
    RST.CocaseI loc rep ns (embedCore <$> cases)
  embedCore (Core.XCaseI loc rep CnsRep ns cases) =
    RST.CaseI loc rep ns (embedCore <$> cases)
  embedCore (Core.Lambda loc rep fv tm) =
    RST.Lambda loc rep fv (embedCore tm)
  embedCore (Core.XCase loc _ pc ns cases) =
    RST.XCase loc pc ns (embedCore <$> cases) -- revisit
  embedCore (Core.PrimLitI64 loc d) =
      RST.PrimLitI64 loc d
  embedCore (Core.PrimLitF64 loc d) =
      RST.PrimLitF64 loc d
  embedCore (Core.PrimLitChar loc d) =
      RST.PrimLitChar loc d
  embedCore (Core.PrimLitString loc d) =
      RST.PrimLitString loc d

instance EmbedCore (Core.TermCase pc) (RST.TermCase pc) where
  embedCore :: Core.TermCase pc -> RST.TermCase pc
  embedCore (Core.MkTermCase loc pat t) =
    RST.MkTermCase loc pat (embedCore t)

instance EmbedCore (Core.TermCaseI pc) (RST.TermCaseI pc) where
  embedCore :: Core.TermCaseI pc -> RST.TermCaseI pc
  embedCore (Core.MkTermCaseI loc pati t) =
    RST.MkTermCaseI loc pati (embedCore t)

instance EmbedCore Core.Command RST.Command where
  embedCore :: Core.Command -> RST.Command
  embedCore (Core.RawApply loc prd cns ) =
      RST.Apply loc (embedCore prd) (embedCore cns)
  embedCore (Core.CocaseOfI loc rep ns t cases) =
      RST.CocaseOfI loc rep ns (embedCore t) (embedCore <$> cases)
  embedCore (Core.CaseOfI loc rep ns t cases) =
      RST.CaseOfI loc rep ns  (embedCore t) (embedCore <$> cases)
  embedCore (Core.CocaseOfCmd loc ns t cases) =
    RST.CocaseOfCmd loc ns (embedCore t) (embedCore <$> cases)
  embedCore (Core.CaseOfCmd loc ns t cases) =
    RST.CaseOfCmd loc ns (embedCore t) (embedCore <$> cases)
  embedCore (Core.Method loc mn cn subst) =
    RST.Method loc mn cn (embedCore subst)
  embedCore (Core.Print loc tm cmd) =
      RST.Print loc (embedCore tm) (embedCore cmd)
  embedCore (Core.Read loc tm) =
      RST.Read loc (embedCore tm)
  embedCore (Core.Jump loc fv) =
      RST.Jump loc fv
  embedCore (Core.ExitSuccess loc) =
      RST.ExitSuccess loc
  embedCore (Core.ExitFailure loc) =
      RST.ExitFailure loc
  embedCore (Core.PrimOp loc op subst) =
      RST.PrimOp loc op (embedCore subst)

---------------------------------------------------------------------------------
-- EmbedCore implementation for declarations
---------------------------------------------------------------------------------

instance EmbedCore (Core.PrdCnsDeclaration pc) (RST.PrdCnsDeclaration pc) where
  embedCore :: Core.PrdCnsDeclaration pc -> RST.PrdCnsDeclaration pc
  embedCore Core.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term } =
      RST.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                              , pcdecl_doc = pcdecl_doc
                              , pcdecl_pc = pcdecl_pc
                              , pcdecl_isRec = pcdecl_isRec
                              , pcdecl_name = pcdecl_name
                              , pcdecl_annot = pcdecl_annot
                              , pcdecl_term = embedCore pcdecl_term
                              }

instance EmbedCore Core.CommandDeclaration RST.CommandDeclaration where
  embedCore :: Core.CommandDeclaration -> RST.CommandDeclaration
  embedCore Core.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
      RST.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                               , cmddecl_doc = cmddecl_doc
                               , cmddecl_name = cmddecl_name
                               , cmddecl_cmd = embedCore cmddecl_cmd
                               }

instance EmbedCore Core.InstanceDeclaration RST.InstanceDeclaration where
  embedCore :: Core.InstanceDeclaration -> RST.InstanceDeclaration
  embedCore Core.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases } =
      RST.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                                , instancedecl_doc = instancedecl_doc
                                , instancedecl_name = instancedecl_name
                                , instancedecl_typ = instancedecl_typ
                                , instancedecl_cases = embedCore <$> instancedecl_cases
                                }

instance EmbedCore Core.Declaration RST.Declaration where
  embedCore :: Core.Declaration -> RST.Declaration
  embedCore (Core.PrdCnsDecl pcrep decl) =
      RST.PrdCnsDecl pcrep (embedCore decl)
  embedCore (Core.CmdDecl decl) =
      RST.CmdDecl (embedCore decl)
  embedCore (Core.DataDecl decl) =
      RST.DataDecl decl
  embedCore (Core.XtorDecl decl) =
      RST.XtorDecl decl
  embedCore (Core.ImportDecl decl) =
      RST.ImportDecl decl
  embedCore (Core.SetDecl decl) =
      RST.SetDecl decl
  embedCore (Core.TyOpDecl decl) =
      RST.TyOpDecl decl
  embedCore (Core.TySynDecl decl) =
      RST.TySynDecl decl
  embedCore (Core.ClassDecl decl) =
      RST.ClassDecl decl
  embedCore (Core.InstanceDecl decl) =
      RST.InstanceDecl (embedCore decl)

---------------------------------------------------------------------------------
-- EmbedCore implementation for a module
---------------------------------------------------------------------------------

instance EmbedCore Core.Module RST.Module where
  embedCore :: Core.Module -> RST.Module
  embedCore Core.MkModule { mod_name, mod_fp, mod_decls } =
      RST.MkModule { mod_name = mod_name
                   , mod_fp = mod_fp
                   , mod_decls = embedCore <$> mod_decls
                   }

