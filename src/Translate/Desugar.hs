module Translate.Desugar
  ( desugarTerm
  , desugarPCTerm
  , desugarProgram
  , desugarCmd
  , desugarEnvironment
  , isDesugaredTerm
  , isDesugaredCommand
  )
  where

import Driver.Environment (Environment(..))
import Syntax.AST.Program qualified as AST
import Syntax.AST.Terms qualified as AST
import Syntax.Common


---------------------------------------------------------------------------------
-- Check if term is desugared
---------------------------------------------------------------------------------

isDesugaredPCTerm :: AST.PrdCnsTerm -> Bool
isDesugaredPCTerm (AST.PrdTerm tm) = isDesugaredTerm tm
isDesugaredPCTerm (AST.CnsTerm tm) = isDesugaredTerm tm

isDesugaredTerm :: AST.Term pc -> Bool
-- Core terms
isDesugaredTerm AST.BoundVar {} = True
isDesugaredTerm AST.FreeVar {} = True
isDesugaredTerm (AST.Xtor _ _ _ _ _ subst) =
  and (isDesugaredPCTerm <$> subst)
isDesugaredTerm (AST.MuAbs _ _ _ _ cmd) =
  isDesugaredCommand cmd
isDesugaredTerm (AST.XMatch _ _ _ _ cases) =
  and ((\AST.MkCmdCase { cmdcase_cmd } -> isDesugaredCommand cmdcase_cmd ) <$> cases)
isDesugaredTerm AST.PrimLitI64{} = True
isDesugaredTerm AST.PrimLitF64{} = True
-- Non-core terms
isDesugaredTerm AST.Dtor{} = False
isDesugaredTerm AST.Case {} = False
isDesugaredTerm AST.Cocase {} = False

isDesugaredCommand :: AST.Command -> Bool
isDesugaredCommand (AST.Apply _ _ prd cns) =
  isDesugaredTerm prd && isDesugaredTerm cns
isDesugaredCommand (AST.Print _ prd cmd) =
  isDesugaredTerm prd && isDesugaredCommand cmd
isDesugaredCommand (AST.Read _ cns) =
  isDesugaredTerm cns
isDesugaredCommand (AST.Jump _ _) = True
isDesugaredCommand (AST.ExitSuccess _) = True
isDesugaredCommand (AST.ExitFailure _) = True
isDesugaredCommand (AST.PrimOp _ _ _ subst) =
  and (isDesugaredPCTerm <$> subst)

---------------------------------------------------------------------------------
-- Desugar Terms
--
-- This translates terms into the core subset of terms.
---------------------------------------------------------------------------------

resVar :: FreeVarName
resVar = MkFreeVarName "$result"


desugarPCTerm :: AST.PrdCnsTerm -> AST.PrdCnsTerm
desugarPCTerm (AST.PrdTerm tm) = AST.PrdTerm $ desugarTerm tm
desugarPCTerm (AST.CnsTerm tm) = AST.CnsTerm $ desugarTerm tm

desugarTerm :: AST.Term pc -> AST.Term pc
desugarTerm (AST.BoundVar loc pc annot idx) =
  AST.BoundVar loc pc annot idx
desugarTerm (AST.FreeVar loc pc annot fv) =
  AST.FreeVar loc pc annot fv
desugarTerm (AST.Xtor loc pc annot ns xt args) =
  AST.Xtor loc pc annot ns xt (desugarPCTerm <$> args)
desugarTerm (AST.MuAbs loc pc annot bs cmd) =
  AST.MuAbs loc pc annot bs (desugarCmd cmd)
desugarTerm (AST.XMatch loc pc annot ns cases) =
  AST.XMatch loc pc annot ns (desugarCmdCase <$> cases)
desugarTerm (AST.PrimLitI64 loc i) =
  AST.PrimLitI64 loc i
desugarTerm (AST.PrimLitF64 loc d) =
  AST.PrimLitF64 loc d
-- we want to desugar e.D(args')
-- Mu k.[(desugar e) >> D (desugar <$> args')[k] ]
desugarTerm (AST.Dtor loc _ _ ns xt t (args1,PrdRep,args2)) =
  let
    args = (desugarPCTerm <$> args1) ++ [AST.CnsTerm $ AST.FreeVar loc CnsRep Nothing resVar] ++ (desugarPCTerm <$> args2)
    cmd = AST.Apply loc Nothing (desugarTerm t)
                           (AST.Xtor loc CnsRep Nothing ns xt args)
  in
    AST.MuAbs loc PrdRep Nothing Nothing $ AST.commandClosing [(Cns, resVar)] $ AST.shiftCmd cmd
desugarTerm (AST.Dtor loc _ _ ns xt t (args1,CnsRep,args2)) =
  let
    args = (desugarPCTerm <$> args1) ++ [AST.PrdTerm $ AST.FreeVar loc PrdRep Nothing resVar] ++ (desugarPCTerm <$> args2)
    cmd = AST.Apply loc Nothing (desugarTerm t)
                                (AST.Xtor loc CnsRep Nothing ns xt args)
  in
    AST.MuAbs loc CnsRep Nothing Nothing $ AST.commandClosing [(Prd, resVar)] $ AST.shiftCmd cmd
-- we want to desugar match t { C (args) => e1 }
-- Mu k.[ (desugar t) >> match {C (args) => (desugar e1) >> k } ]
desugarTerm (AST.Case loc _ ns t cases)   =
  let
    desugarMatchCase (AST.MkTermCase _ xt args t) = AST.MkCmdCase loc xt args  $ AST.Apply loc Nothing (desugarTerm t) (AST.FreeVar loc CnsRep Nothing resVar)
    cmd = AST.Apply loc Nothing (desugarTerm t) (AST.XMatch loc CnsRep Nothing ns  (desugarMatchCase <$> cases))
  in
    AST.MuAbs loc PrdRep Nothing Nothing $ AST.commandClosing [(Cns, resVar)] $ AST.shiftCmd cmd
-- we want to desugar comatch { D(args) => e }
-- comatch { D(args)[k] => (desugar e) >> k }
desugarTerm (AST.Cocase loc _ ns cocases) =
  let
    desugarComatchCase (AST.MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Cns,Nothing)] ++ as2 in
      AST.MkCmdCase loc xt args $ AST.Apply loc Nothing (desugarTerm t) (AST.BoundVar loc CnsRep Nothing (0,length as1))
  in
    AST.XMatch loc PrdRep Nothing ns $ desugarComatchCase <$> cocases

desugarCmdCase :: AST.CmdCase -> AST.CmdCase
desugarCmdCase (AST.MkCmdCase loc xt args cmd) = 
  AST.MkCmdCase loc xt args (desugarCmd cmd)

desugarCmd :: AST.Command -> AST.Command
desugarCmd (AST.Apply loc kind prd cns) =
  AST.Apply loc kind (desugarTerm prd) (desugarTerm cns)
desugarCmd (AST.Print loc prd cmd) =
  AST.Print loc (desugarTerm prd) (desugarCmd cmd)
desugarCmd (AST.Read loc cns) =
  AST.Read loc (desugarTerm cns)
desugarCmd (AST.Jump loc fv) =
  AST.Jump loc fv
desugarCmd (AST.ExitSuccess loc) =
  AST.ExitSuccess loc
desugarCmd (AST.ExitFailure loc) =
  AST.ExitFailure loc
desugarCmd (AST.PrimOp loc pt op subst) =
  AST.PrimOp loc pt op (desugarPCTerm <$> subst)

---------------------------------------------------------------------------------
-- Translate Program
---------------------------------------------------------------------------------

desugarDecl :: AST.Declaration -> AST.Declaration
desugarDecl (AST.PrdCnsDecl loc doc pc isRec fv annot tm) =
  AST.PrdCnsDecl loc doc pc isRec fv annot (desugarTerm tm)
desugarDecl (AST.CmdDecl loc doc fv cmd) =
  AST.CmdDecl loc doc fv (desugarCmd cmd)
desugarDecl (AST.DataDecl loc doc decl) =
  AST.DataDecl loc doc decl
desugarDecl (AST.XtorDecl loc doc dc xt args ret) =
  AST.XtorDecl loc doc dc xt args ret
desugarDecl (AST.ImportDecl loc doc mn) =
  AST.ImportDecl loc doc mn
desugarDecl (AST.SetDecl loc doc txt) =
  AST.SetDecl loc doc txt
desugarDecl (AST.TyOpDecl loc doc op prec assoc ty) =
  AST.TyOpDecl loc doc op prec assoc ty

desugarProgram :: AST.Program -> AST.Program
desugarProgram ps = desugarDecl <$> ps

desugarEnvironment :: Environment -> Environment
desugarEnvironment (MkEnvironment { prdEnv, cnsEnv, cmdEnv, declEnv }) =
    MkEnvironment
      { prdEnv = (\(tm,loc,tys) -> (desugarTerm tm,loc,tys)) <$> prdEnv
      , cnsEnv = (\(tm,loc,tys) -> (desugarTerm tm,loc,tys)) <$> cnsEnv
      , cmdEnv = (\(cmd,loc) -> (desugarCmd cmd,loc)) <$> cmdEnv
      , declEnv = declEnv
      }