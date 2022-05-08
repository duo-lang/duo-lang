module Translate.ForgetTypes where

import Syntax.AST.Program qualified as AST
import Syntax.AST.Terms qualified as AST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.Common.TypesPol qualified as RST

forgetTypesSubst :: AST.Substitution  -> RST.Substitution 
forgetTypesSubst = fmap forgetTypesPCTerm

forgetTypesSubstI :: AST.SubstitutionI pc  -> RST.SubstitutionI pc
forgetTypesSubstI (subst1, pc, subst2) = (forgetTypesSubst subst1, pc, forgetTypesSubst subst2)

forgetTypesPCTerm :: AST.PrdCnsTerm  -> RST.PrdCnsTerm
forgetTypesPCTerm (AST.PrdTerm tm) = RST.PrdTerm (forgetTypesTerm tm)
forgetTypesPCTerm (AST.CnsTerm tm) = RST.CnsTerm (forgetTypesTerm tm)

forgetTypesPat :: AST.Pattern -> RST.Pattern
forgetTypesPat (AST.XtorPat loc xt args) = RST.XtorPat loc xt args

forgetTypesPatI :: AST.PatternI -> RST.PatternI
forgetTypesPatI (AST.XtorPatI loc xt args) = RST.XtorPatI loc xt args

forgetTypesCmdCase :: AST.CmdCase  -> RST.CmdCase
forgetTypesCmdCase AST.MkCmdCase { cmdcase_loc, cmdcase_pat, cmdcase_cmd } =
    RST.MkCmdCase
      { cmdcase_loc = cmdcase_loc
      , cmdcase_pat = forgetTypesPat cmdcase_pat
      , cmdcase_cmd = forgetTypesCommand cmdcase_cmd 
      }

forgetTypesTermCase :: AST.TermCase pc -> RST.TermCase pc
forgetTypesTermCase AST.MkTermCase { tmcase_loc, tmcase_pat, tmcase_term } =
    RST.MkTermCase
      { tmcase_loc = tmcase_loc
      , tmcase_pat = forgetTypesPat tmcase_pat
      , tmcase_term = forgetTypesTerm tmcase_term 
      }

forgetTypesTermCaseI :: AST.TermCaseI pc -> RST.TermCaseI pc
forgetTypesTermCaseI AST.MkTermCaseI { tmcasei_loc, tmcasei_pat, tmcasei_term } =
    RST.MkTermCaseI
      { tmcasei_loc = tmcasei_loc
      , tmcasei_pat = forgetTypesPatI tmcasei_pat
      , tmcasei_term = forgetTypesTerm tmcasei_term 
      }

forgetTypesTerm :: AST.Term pc -> RST.Term pc
-- Core constructs
forgetTypesTerm (AST.BoundVar loc pc _ty idx) =
    RST.BoundVar loc pc idx
forgetTypesTerm (AST.FreeVar loc pc _ty nm) =
    RST.FreeVar loc pc nm
forgetTypesTerm (AST.Xtor loc _annot pc _ty ns xt subst) =
    RST.Xtor loc pc ns xt (forgetTypesSubst subst)
forgetTypesTerm (AST.XCase loc _annot pc _ty ns cases) =
    RST.XCase loc pc ns (forgetTypesCmdCase <$> cases)
forgetTypesTerm (AST.MuAbs loc _annot pc _ty bs cmd) =
    RST.MuAbs loc pc bs (forgetTypesCommand cmd)
-- Primitive constructs
forgetTypesTerm (AST.PrimLitI64 loc i) =
    RST.PrimLitI64 loc i
forgetTypesTerm (AST.PrimLitF64 loc d) =
    RST.PrimLitF64 loc d



forgetTypesCommand :: AST.Command -> RST.Command
forgetTypesCommand (AST.Apply loc _annot _kind prd cns) =
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