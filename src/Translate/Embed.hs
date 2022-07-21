module Translate.Embed where

import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Program qualified as Core
import Sugar.Core qualified as Core
import Syntax.Common.PrdCns
import Syntax.Common.TypesPol
import Translate.Reparse ()
import qualified Syntax.Common.TypesPol as TST
import qualified Syntax.Common.TypesPol as Core

embedCmdCase :: Core.CmdCase -> RST.CmdCase
embedCmdCase Core.MkCmdCase {cmdcase_loc, cmdcase_pat, cmdcase_cmd } =
    RST.MkCmdCase { cmdcase_loc = cmdcase_loc
                  , cmdcase_pat = cmdcase_pat
                  , cmdcase_cmd = embedCoreCommand cmdcase_cmd
                  }

embedInstanceCase :: Core.InstanceCase -> RST.InstanceCase
embedInstanceCase Core.MkInstanceCase {instancecase_loc, instancecase_pat, instancecase_cmd } =
    RST.MkInstanceCase { instancecase_loc = instancecase_loc
                       , instancecase_pat = instancecase_pat
                       , instancecase_cmd = embedCoreCommand instancecase_cmd
                       }

embedPCTerm :: Core.PrdCnsTerm -> RST.PrdCnsTerm
embedPCTerm (Core.PrdTerm tm) = RST.PrdTerm (embedCoreTerm tm)
embedPCTerm (Core.CnsTerm tm) = RST.CnsTerm (embedCoreTerm tm)

embedSubst :: Core.Substitution -> RST.Substitution
embedSubst = fmap embedPCTerm

embedCoreTerm :: Core.Term pc -> RST.Term pc
embedCoreTerm (Core.BoundVar loc rep idx) =
    RST.BoundVar loc rep idx
embedCoreTerm (Core.FreeVar loc rep idx) =
    RST.FreeVar loc rep idx
embedCoreTerm (Core.RawXtor loc rep ns xs subst) =
    RST.Xtor loc rep ns xs (embedSubst subst)
embedCoreTerm (Core.RawCase loc rep ns cases) =
    RST.XCase loc rep ns (embedCmdCase <$> cases)
embedCoreTerm (Core.RawMuAbs loc rep b cmd) =
    RST.MuAbs loc rep b (embedCoreCommand cmd)
embedCoreTerm (Core.CocaseOf loc rep ns t cases) =
    RST.CocaseOf loc rep ns (embedCoreTerm t) (embedTermCase <$> cases)
embedCoreTerm (Core.CaseOf loc rep ns t cases) = RST.CaseOf loc rep ns (embedCoreTerm t) (embedTermCase <$> cases)    
embedCoreTerm (Core.Dtor loc rep ns xt t (subst,r,subst2)) = RST.Dtor loc rep ns xt (embedCoreTerm t) (embedSubst subst, r, embedSubst subst2)
embedCoreTerm (Core.Semi loc rep ns xt (subst,r,subst2) t ) = RST.Semi loc rep ns xt (embedSubst subst, r, embedSubst subst2) (embedCoreTerm t) 
embedCoreTerm (Core.XCaseI loc rep PrdRep ns cases) = RST.CocaseI loc rep ns (embedTermCaseI <$> cases)
embedCoreTerm (Core.XCaseI loc rep CnsRep ns cases) = RST.CaseI loc rep ns (embedTermCaseI <$> cases)
embedCoreTerm (Core.Lambda loc rep fv tm)  = RST.Lambda loc rep fv (embedCoreTerm tm) 
embedCoreTerm (Core.XCase loc _ pc ns cases) = RST.XCase loc pc ns (embedCmdCase <$> cases) -- revisit
embedCoreTerm (Core.PrimLitI64 loc d) =
    RST.PrimLitI64 loc d
embedCoreTerm (Core.PrimLitF64 loc d) =
    RST.PrimLitF64 loc d

embedTermCase :: Core.TermCase pc -> RST.TermCase pc
embedTermCase (Core.MkTermCase loc pat t) = RST.MkTermCase loc pat (embedCoreTerm t)

embedTermCaseI :: Core.TermCaseI pc -> RST.TermCaseI pc
embedTermCaseI (Core.MkTermCaseI loc pati t) = RST.MkTermCaseI loc pati (embedCoreTerm t)

embedCoreCommand :: Core.Command -> RST.Command
embedCoreCommand (Core.RawApply loc prd cns ) =
    RST.Apply loc (embedCoreTerm prd) (embedCoreTerm cns)
embedCoreCommand (Core.CocaseOfI loc rep ns t cases) =
    RST.CocaseOfI loc rep ns (embedCoreTerm t) (embedTermCaseI <$> cases) 
embedCoreCommand (Core.CaseOfI loc rep ns t cases) =
    RST.CaseOfI loc rep ns  (embedCoreTerm t) (embedTermCaseI <$> cases) 
embedCoreCommand (Core.CocaseOfCmd loc ns t cases) = RST.CocaseOfCmd loc ns (embedCoreTerm t) (embedCmdCase <$> cases)
embedCoreCommand (Core.CaseOfCmd loc ns t cases) = RST.CaseOfCmd loc ns (embedCoreTerm t) (embedCmdCase <$> cases) 
embedCoreCommand (Core.Print loc tm cmd) =
    RST.Print loc (embedCoreTerm tm) (embedCoreCommand cmd)
embedCoreCommand (Core.Read loc tm) =
    RST.Read loc (embedCoreTerm tm)
embedCoreCommand (Core.Jump loc fv) =
    RST.Jump loc fv
embedCoreCommand (Core.ExitSuccess loc) =
    RST.ExitSuccess loc
embedCoreCommand (Core.ExitFailure loc) =
    RST.ExitFailure loc
embedCoreCommand (Core.PrimOp loc ty op subst) =
    RST.PrimOp loc ty op (embedSubst subst)


embedCoreProg :: Core.Program -> RST.Program
embedCoreProg = fmap embedCoreDecl

embedPrdCnsDeclaration :: Core.PrdCnsDeclaration pc -> RST.PrdCnsDeclaration pc
embedPrdCnsDeclaration Core.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term } =
    RST.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                            , pcdecl_doc = pcdecl_doc
                            , pcdecl_pc = pcdecl_pc
                            , pcdecl_isRec = pcdecl_isRec
                            , pcdecl_name = pcdecl_name
                            , pcdecl_annot = embedTypeScheme pcdecl_annot
                            , pcdecl_term = embedCoreTerm pcdecl_term
                            }

embedCommandDeclaration :: Core.CommandDeclaration -> RST.CommandDeclaration
embedCommandDeclaration Core.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
    RST.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                             , cmddecl_doc = cmddecl_doc
                             , cmddecl_name = cmddecl_name
                             , cmddecl_cmd = embedCoreCommand cmddecl_cmd
                             }

embedInstanceDeclaration :: Core.InstanceDeclaration -> RST.InstanceDeclaration
embedInstanceDeclaration Core.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases } =
    RST.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                              , instancedecl_doc = instancedecl_doc
                              , instancedecl_name = instancedecl_name
                              , instancedecl_typ = instancedecl_typ
                              , instancedecl_cases = embedInstanceCase <$> instancedecl_cases
                              }

embedCoreDecl :: Core.Declaration -> RST.Declaration
embedCoreDecl (Core.PrdCnsDecl pcrep decl) =
    RST.PrdCnsDecl pcrep (embedPrdCnsDeclaration decl)
embedCoreDecl (Core.CmdDecl decl) =
    RST.CmdDecl (embedCommandDeclaration decl)
embedCoreDecl (Core.DataDecl decl) =
    RST.DataDecl decl
embedCoreDecl (Core.XtorDecl decl) =
    RST.XtorDecl decl
embedCoreDecl (Core.ImportDecl decl) =
    RST.ImportDecl decl
embedCoreDecl (Core.SetDecl decl) =
    RST.SetDecl decl
embedCoreDecl (Core.TyOpDecl decl) =
    RST.TyOpDecl decl
embedCoreDecl (Core.TySynDecl decl) =
    RST.TySynDecl decl
embedCoreDecl (Core.ClassDecl decl) =
    RST.ClassDecl decl
embedCoreDecl (Core.InstanceDecl decl) =
    RST.InstanceDecl (embedInstanceDeclaration decl)

embedTSTCmdCase :: TST.CmdCase -> Core.CmdCase
embedTSTCmdCase TST.MkCmdCase {cmdcase_loc, cmdcase_pat, cmdcase_cmd } =
    Core.MkCmdCase { cmdcase_loc = cmdcase_loc
                   , cmdcase_pat = cmdcase_pat
                   , cmdcase_cmd = embedTSTCommand cmdcase_cmd
                   }

embedTSTInstanceCase :: TST.InstanceCase -> Core.InstanceCase
embedTSTInstanceCase TST.MkInstanceCase {instancecase_loc, instancecase_pat, instancecase_cmd } =
    Core.MkInstanceCase { instancecase_loc = instancecase_loc
                        , instancecase_pat = instancecase_pat
                        , instancecase_cmd = embedTSTCommand instancecase_cmd
                        }

embedTSTPCTerm :: TST.PrdCnsTerm -> Core.PrdCnsTerm
embedTSTPCTerm (TST.PrdTerm tm) = Core.PrdTerm (embedTSTTerm tm)
embedTSTPCTerm (TST.CnsTerm tm) = Core.CnsTerm (embedTSTTerm tm)


embedTSTSubst :: TST.Substitution -> Core.Substitution
embedTSTSubst = fmap embedTSTPCTerm

embedTSTTerm :: TST.Term pc -> Core.Term pc
embedTSTTerm (TST.BoundVar loc rep _ty idx) =
    Core.BoundVar loc rep idx
embedTSTTerm (TST.FreeVar loc rep _ty idx) =
    Core.FreeVar loc rep idx
embedTSTTerm (TST.Xtor loc annot rep _ty ns xs subst) =
    Core.Xtor loc annot rep ns xs (embedTSTSubst subst)
embedTSTTerm (TST.XCase loc annot rep _ty ns cases) =
    Core.XCase loc annot rep ns (embedTSTCmdCase <$> cases)
embedTSTTerm (TST.MuAbs loc annot rep _ty b cmd) =
    Core.MuAbs loc annot rep b (embedTSTCommand cmd)
embedTSTTerm (TST.PrimLitI64 loc i) =
    Core.PrimLitI64 loc i
embedTSTTerm (TST.PrimLitF64 loc d) =
    Core.PrimLitF64 loc d


embedTSTCommand :: TST.Command -> Core.Command
embedTSTCommand (TST.Apply loc annot _kind prd cns ) =
    Core.Apply loc annot (embedTSTTerm prd) (embedTSTTerm cns)
embedTSTCommand (TST.Print loc tm cmd) =
    Core.Print loc (embedTSTTerm tm) (embedTSTCommand cmd)
embedTSTCommand (TST.Read loc tm) =
    Core.Read loc (embedTSTTerm tm)
embedTSTCommand (TST.Jump loc fv) =
    Core.Jump loc fv
embedTSTCommand (TST.ExitSuccess loc) =
    Core.ExitSuccess loc
embedTSTCommand (TST.ExitFailure loc) =
    Core.ExitFailure loc
embedTSTCommand (TST.PrimOp loc ty op subst) =
    Core.PrimOp loc ty op (embedTSTSubst subst)

embedTSTProg :: TST.Program -> Core.Program
embedTSTProg = fmap embedTSTDecl

embedTypeScheme :: TST.TypeScheme pol -> Core.TypeScheme pol
embedTypeScheme (TypeScheme loc tvars mt) = Core.TypeScheme loc tvars mt

embedTSTPrdCnsDecl :: TST.PrdCnsDeclaration pc -> Core.PrdCnsDeclaration pc
embedTSTPrdCnsDecl TST.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term } =
    Core.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                             , pcdecl_doc = pcdecl_doc
                             , pcdecl_pc = pcdecl_pc
                             , pcdecl_isRec = pcdecl_isRec
                             , pcdecl_name = pcdecl_name
                             , pcdecl_annot = pcdecl_annot
                             , pcdecl_term = embedTSTTerm pcdecl_term
                             }

embedTSTCommandDecl :: TST.CommandDeclaration -> Core.CommandDeclaration
embedTSTCommandDecl TST.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
    Core.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                              , cmddecl_doc = cmddecl_doc
                              , cmddecl_name = cmddecl_name
                              , cmddecl_cmd = embedTSTCommand cmddecl_cmd
                              }

embedTSTInstanceDeclaration :: TST.InstanceDeclaration -> Core.InstanceDeclaration
embedTSTInstanceDeclaration TST.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases } =
    Core.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                               , instancedecl_doc = instancedecl_doc
                               , instancedecl_name = instancedecl_name
                               , instancedecl_typ = instancedecl_typ
                               , instancedecl_cases = embedTSTInstanceCase <$> instancedecl_cases
                               }


embedTSTDecl :: TST.Declaration -> Core.Declaration
embedTSTDecl (TST.PrdCnsDecl pcrep decl) =
    Core.PrdCnsDecl pcrep (embedTSTPrdCnsDecl decl)
embedTSTDecl (TST.CmdDecl decl) =
    Core.CmdDecl (embedTSTCommandDecl decl)
embedTSTDecl (TST.DataDecl decl) =
    Core.DataDecl decl
embedTSTDecl (TST.XtorDecl decl) =
    Core.XtorDecl decl
embedTSTDecl (TST.ImportDecl decl) =
    Core.ImportDecl decl
embedTSTDecl (TST.SetDecl decl) =
    Core.SetDecl decl
embedTSTDecl (TST.TyOpDecl decl) =
    Core.TyOpDecl decl
embedTSTDecl (TST.TySynDecl decl) =
    Core.TySynDecl decl
embedTSTDecl (TST.ClassDecl decl) =
    Core.ClassDecl decl
embedTSTDecl (TST.InstanceDecl decl) =
    Core.InstanceDecl (embedTSTInstanceDeclaration decl)

   