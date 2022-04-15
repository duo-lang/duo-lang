module Translate.ForgetTypes where

import Syntax.AST.Program qualified as AST
import Syntax.AST.Terms qualified as AST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.RST.Types qualified as RST
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
forgetTypesTerm (AST.PrimLitI64 loc i) =
    RST.PrimLitI64 loc i
forgetTypesTerm (AST.PrimLitF64 loc d) =
    RST.PrimLitF64 loc d
forgetTypesTerm (AST.CaseCnsPrdI _loc _annot _ns _tmcasesI) =
    error "not yet implemented"
forgetTypesTerm (AST.CaseCnsCnsI _loc _annot _ns _tmcasesI) =
    error "not yet implemented"
forgetTypesTerm (AST.Semicolon _loc _rep _annot _ns _xt (_args1,_pcrep,_args2) _t) =
    error "not yet implemented"
forgetTypesTerm (AST.CocaseCns _loc _rep _annot _ns _t _tmcasesI) =
    error "not yet implemented" 
forgetTypesTerm (AST.CocaseCnsI _loc _annot _ns _tmcasesI) =
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
forgetTypesCommand (AST.CasePrdCmd _loc _ns _t _cases) =
    error "not yet implemented"
forgetTypesCommand (AST.CasePrdPrdI _loc _ns _t _cases) =
    error "not yet implemented"
forgetTypesCommand (AST.CasePrdCnsI _loc _ns _t _cases) =
    error "not yet implemented"
forgetTypesCommand (AST.CocaseCnsCmd _loc _ns _t _cases) =
    error "not yet implemented"
forgetTypesCommand (AST.CocaseCnsPrdI _loc _ns _t _cases) =
    error "not yet implemented"
forgetTypesCommand (AST.CocaseCnsCnsI _loc _ns _t _cases) =
    error "not yet implemented"


forgetAnnot :: RST.TopAnnot pol -> Maybe (RST.TypeScheme pol)
forgetAnnot (RST.Annotated tys) = Just tys
forgetAnnot (RST.Inferred _) = Nothing

forgetTypesDecl :: AST.Declaration  -> RST.Declaration 
forgetTypesDecl (AST.PrdCnsDecl loc doc pcrep isrec fv annot tm) =
    RST.PrdCnsDecl loc doc pcrep isrec fv (forgetAnnot annot) (forgetTypesTerm tm)
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
forgetTypesDecl (AST.TySynDecl loc doc nm ty) =
    RST.TySynDecl loc doc nm ty

forgetTypesProgram :: AST.Program -> RST.Program
forgetTypesProgram = fmap forgetTypesDecl