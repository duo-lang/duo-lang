module Translate.ForgetTypes where

import Syntax.AST.Program qualified as AST
import Syntax.AST.Terms qualified as AST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.Common (PrdCnsRep(PrdRep),PrdCnsRep(CnsRep))


forgetTypesSubst :: AST.Substitution  -> RST.Substitution 
forgetTypesSubst = fmap forgetTypesPCTerm

forgetTypesSubstI :: AST.SubstitutionI pc  -> RST.SubstitutionI pc
forgetTypesSubstI (subst1, pc, subst2) = (forgetTypesSubst subst1, pc, forgetTypesSubst subst2)

forgetTypesPCTerm :: AST.PrdCnsTerm  -> RST.PrdCnsTerm
forgetTypesPCTerm (AST.PrdTerm tm) = RST.PrdTerm (forgetTypesTerm tm)
forgetTypesPCTerm (AST.CnsTerm tm) = RST.CnsTerm (forgetTypesTerm tm)

forgetTypesCmdCase :: AST.CmdCase  -> RST.CmdCase
forgetTypesCmdCase AST.MkCmdCase { cmdcase_ext, cmdcase_name, cmdcase_args, cmdcase_cmd } =
    RST.MkCmdCase
      { cmdcase_ext = cmdcase_ext
      , cmdcase_name = cmdcase_name
      , cmdcase_args = cmdcase_args
      , cmdcase_cmd = forgetTypesCommand cmdcase_cmd 
      }

forgetTypesTermCase :: AST.TermCase pc -> RST.TermCase pc
forgetTypesTermCase AST.MkTermCase { tmcase_ext, tmcase_name, tmcase_args, tmcase_term } =
    RST.MkTermCase
      { tmcase_ext = tmcase_ext
      , tmcase_name = tmcase_name
      , tmcase_args = tmcase_args
      , tmcase_term = forgetTypesTerm tmcase_term 
      }

forgetTypesTermCaseI :: AST.TermCaseI pc -> RST.TermCaseI pc
forgetTypesTermCaseI AST.MkTermCaseI { tmcasei_ext, tmcasei_name, tmcasei_args, tmcasei_term } =
    RST.MkTermCaseI
      { tmcasei_ext = tmcasei_ext
      , tmcasei_name = tmcasei_name
      , tmcasei_args = tmcasei_args
      , tmcasei_term = forgetTypesTerm tmcasei_term 
      }

forgetTypesTerm :: AST.Term pc -> RST.Term pc
forgetTypesTerm (AST.BoundVar loc pc _annot idx) =
    RST.BoundVar loc pc idx
forgetTypesTerm (AST.FreeVar loc pc _annot nm) =
    RST.FreeVar loc pc nm
forgetTypesTerm (AST.Xtor loc pc _annot ns xt subst) =
    RST.Xtor loc pc ns xt (forgetTypesSubst subst)
forgetTypesTerm (AST.XMatch loc pc _annot ns cases) =
    RST.XMatch loc pc ns (forgetTypesCmdCase <$> cases)
forgetTypesTerm (AST.MuAbs loc pc _annot bs cmd) =
    RST.MuAbs loc pc bs (forgetTypesCommand cmd)
forgetTypesTerm (AST.Dtor loc pc _annot ns xt tm subst) =
    RST.Dtor loc pc ns xt (forgetTypesTerm tm) (forgetTypesSubstI subst)
forgetTypesTerm (AST.Case loc PrdRep _annot ns tm cases) =
    RST.Case loc ns (forgetTypesTerm tm) (forgetTypesTermCase <$> cases)
forgetTypesTerm (AST.CocasePrdI loc _annot ns cases) =
    RST.Cocase loc ns (forgetTypesTermCaseI <$> cases)
forgetTypesTerm (AST.PrimLitI64 loc i) =
    RST.PrimLitI64 loc i
forgetTypesTerm (AST.PrimLitF64 loc d) =
    RST.PrimLitF64 loc d
forgetTypesTerm (AST.CaseCnsPrdI loc annot ns tmcasesI) = error "not yet implemented"
forgetTypesTerm (AST.CaseCnsCnsI loc annot ns tmcasesI) = error "not yet implemented"
forgetTypesTerm (AST.Semicolon loc rep annot ns xt (args1,pcrep,args2) t) = error "not yet implemented"
forgetTypesTerm (AST.CocaseCns loc rep annot ns t tmcasesI) = error "not yet implemented" 
forgetTypesTerm (AST.CocaseCnsI loc annot ns tmcasesI) = error "not yet implemented"
forgetTypesTerm (AST.Case loc CnsRep _annot ns tm cases) =
    error "not yet implemented"





forgetTypesCommand :: AST.Command -> RST.Command
forgetTypesCommand (AST.Apply loc _kind prd cns) =
    RST.Apply loc (forgetTypesTerm prd) (forgetTypesTerm cns)
forgetTypesCommand (AST.Print loc tm cmd) =
    RST.Print loc (forgetTypesTerm tm) (forgetTypesCommand cmd)
forgetTypesCommand (AST.Read loc tm) =
    RST.Read loc (forgetTypesTerm tm)
forgetTypesCommand (AST.Jump loc fv) =
    RST.Jump loc fv
forgetTypesCommand (AST.ExitSuccess loc) =
    RST.ExitSuccess loc
forgetTypesCommand (AST.ExitFailure loc) =
    RST.ExitFailure loc
forgetTypesCommand (AST.PrimOp loc ty op subst) =
    RST.PrimOp loc ty op (forgetTypesSubst subst)
forgetTypesCommand (AST.CasePrdCmd loc ns t cases) = error "not yet implemented"
forgetTypesCommand (AST.CasePrdPrdI loc ns t cases) = error "not yet implemented"
forgetTypesCommand (AST.CasePrdCnsI loc ns t cases) = error "not yet implemented"
forgetTypesCommand (AST.CocaseCnsCmd loc ns t cases) = error "not yet implemented"
forgetTypesCommand (AST.CocaseCnsPrdI loc ns t cases) = error "not yet implemented"
forgetTypesCommand (AST.CocaseCnsCnsI loc ns t cases) = error "not yet implemented"


forgetTypesDecl :: AST.Declaration  -> RST.Declaration 
forgetTypesDecl (AST.PrdCnsDecl loc doc pcrep isrec fv annot tm) =
    RST.PrdCnsDecl loc doc pcrep isrec fv annot (forgetTypesTerm tm)
forgetTypesDecl (AST.CmdDecl loc doc fv cmd) =
    RST.CmdDecl loc doc fv (forgetTypesCommand cmd)
forgetTypesDecl (AST.DataDecl loc doc decl) =
    RST.DataDecl loc doc decl
forgetTypesDecl (AST.XtorDecl loc doc dc xt args eo) =
    RST.XtorDecl loc doc dc xt args eo
forgetTypesDecl (AST.ImportDecl loc doc mn) =
    RST.ImportDecl loc doc mn
forgetTypesDecl (AST.SetDecl loc doc txt) =
    RST.SetDecl loc doc txt
forgetTypesDecl (AST.TyOpDecl loc doc op prec assoc tn) =
    RST.TyOpDecl loc doc op prec assoc tn

forgetTypesProgram :: AST.Program -> RST.Program
forgetTypesProgram = fmap forgetTypesDecl