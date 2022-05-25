module Translate.Embed where

import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Program qualified as Core
import Sugar.Core qualified as Core
import Syntax.Common.PrdCns

embedCmdCase :: Core.CmdCase -> RST.CmdCase
embedCmdCase Core.MkCmdCase {cmdcase_loc, cmdcase_pat, cmdcase_cmd } =
    RST.MkCmdCase { cmdcase_loc = cmdcase_loc
                  , cmdcase_pat = cmdcase_pat
                  , cmdcase_cmd = embedCoreCommand cmdcase_cmd
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
embedCoreTerm (Core.PrimLitI64 loc i) =
    RST.PrimLitI64 loc i
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

embedCoreDecl :: Core.Declaration -> RST.Declaration
embedCoreDecl (Core.PrdCnsDecl loc doc rep isRec fv _tys tm) =
    RST.PrdCnsDecl loc doc rep isRec fv Nothing (embedCoreTerm tm)
embedCoreDecl (Core.CmdDecl loc doc fv cmd) =
    RST.CmdDecl loc doc fv (embedCoreCommand cmd)
embedCoreDecl (Core.DataDecl loc doc decl) =
    RST.DataDecl loc doc decl
embedCoreDecl (Core.XtorDecl loc doc dc xt knd eo) =
    RST.XtorDecl loc doc dc xt knd eo
embedCoreDecl (Core.ImportDecl loc doc mn) =
    RST.ImportDecl loc doc mn
embedCoreDecl (Core.SetDecl loc doc txt) =
    RST.SetDecl loc doc txt
embedCoreDecl (Core.TyOpDecl loc doc op prec assoc ty) =
    RST.TyOpDecl loc doc op prec assoc ty
embedCoreDecl (Core.TySynDecl loc doc nm ty) =
    RST.TySynDecl loc doc nm ty

embedASTCmdCase :: TST.CmdCase -> Core.CmdCase
embedASTCmdCase TST.MkCmdCase {cmdcase_loc, cmdcase_pat, cmdcase_cmd } =
    Core.MkCmdCase { cmdcase_loc = cmdcase_loc
                  , cmdcase_pat = cmdcase_pat
                  , cmdcase_cmd = embedASTCommand cmdcase_cmd
                  }

embedASTPCTerm :: TST.PrdCnsTerm -> Core.PrdCnsTerm
embedASTPCTerm (TST.PrdTerm tm) = Core.PrdTerm (embedASTTerm tm)
embedASTPCTerm (TST.CnsTerm tm) = Core.CnsTerm (embedASTTerm tm)


embedASTSubst :: TST.Substitution -> Core.Substitution
embedASTSubst = fmap embedASTPCTerm

embedASTTerm :: TST.Term pc -> Core.Term pc
embedASTTerm (TST.BoundVar loc rep _ty idx) =
    Core.BoundVar loc rep idx
embedASTTerm (TST.FreeVar loc rep _ty idx) =
    Core.FreeVar loc rep idx
embedASTTerm (TST.Xtor loc annot rep _ty ns xs subst) =
    Core.Xtor loc annot rep ns xs (embedASTSubst subst)
embedASTTerm (TST.XCase loc annot rep _ty ns cases) =
    Core.XCase loc annot rep ns (embedASTCmdCase <$> cases)
embedASTTerm (TST.MuAbs loc annot rep _ty b cmd) =
    Core.MuAbs loc annot rep b (embedASTCommand cmd)
embedASTTerm (TST.PrimLitI64 loc i) =
    Core.PrimLitI64 loc i
embedASTTerm (TST.PrimLitF64 loc d) =
    Core.PrimLitF64 loc d


embedASTCommand :: TST.Command -> Core.Command
embedASTCommand (TST.Apply loc annot _kind prd cns ) =
    Core.Apply loc annot (embedASTTerm prd) (embedASTTerm cns)
embedASTCommand (TST.Print loc tm cmd) =
    Core.Print loc (embedASTTerm tm) (embedASTCommand cmd)
embedASTCommand (TST.Read loc tm) =
    Core.Read loc (embedASTTerm tm)
embedASTCommand (TST.Jump loc fv) =
    Core.Jump loc fv
embedASTCommand (TST.ExitSuccess loc) =
    Core.ExitSuccess loc
embedASTCommand (TST.ExitFailure loc) =
    Core.ExitFailure loc
embedASTCommand (TST.PrimOp loc ty op subst) =
    Core.PrimOp loc ty op (embedASTSubst subst)

embedASTProg :: TST.Program -> Core.Program
embedASTProg = fmap embedASTDecl

embedASTDecl :: TST.Declaration -> Core.Declaration
embedASTDecl (TST.PrdCnsDecl loc doc rep isRec fv _tys tm) =
    Core.PrdCnsDecl loc doc rep isRec fv Nothing (embedASTTerm tm)
embedASTDecl (TST.CmdDecl loc doc fv cmd) =
    Core.CmdDecl loc doc fv (embedASTCommand cmd)
embedASTDecl (TST.DataDecl loc doc decl) =
    Core.DataDecl loc doc decl
embedASTDecl (TST.XtorDecl loc doc dc xt knd eo) =
    Core.XtorDecl loc doc dc xt knd eo
embedASTDecl (TST.ImportDecl loc doc mn) =
    Core.ImportDecl loc doc mn
embedASTDecl (TST.SetDecl loc doc txt) =
    Core.SetDecl loc doc txt
embedASTDecl (TST.TyOpDecl loc doc op prec assoc ty) =
    Core.TyOpDecl loc doc op prec assoc ty
embedASTDecl (TST.TySynDecl loc doc nm ty) =
    Core.TySynDecl loc doc nm ty    

   