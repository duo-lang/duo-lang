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
import Syntax.AST.Terms
import Syntax.Common
import Syntax.AST.Program ( Declaration(..), Program)

---------------------------------------------------------------------------------
-- Check if term is desugared
---------------------------------------------------------------------------------

isDesugaredPCTerm :: PrdCnsTerm -> Bool
isDesugaredPCTerm (PrdTerm tm) = isDesugaredTerm tm
isDesugaredPCTerm (CnsTerm tm) = isDesugaredTerm tm

isDesugaredTerm :: Term pc -> Bool
-- Core terms
isDesugaredTerm BoundVar {} = True
isDesugaredTerm FreeVar {} = True
isDesugaredTerm (Xtor _ _ _ _ _ subst) = and (isDesugaredPCTerm <$> subst)
isDesugaredTerm (MuAbs _ _ _ _ cmd) = isDesugaredCommand cmd
isDesugaredTerm (XMatch _ _ _ _ cases) = and ((\MkCmdCase { cmdcase_cmd } -> isDesugaredCommand cmdcase_cmd ) <$> cases)
isDesugaredTerm PrimLitI64{} = True
isDesugaredTerm PrimLitF64{} = True
-- Non-core terms
isDesugaredTerm Dtor{} = False
isDesugaredTerm Case {} = False
isDesugaredTerm Cocase {} = False

isDesugaredCommand :: Command -> Bool
isDesugaredCommand (Apply _ _ prd cns) = isDesugaredTerm prd && isDesugaredTerm cns
isDesugaredCommand (Print _ prd cmd) = isDesugaredTerm prd && isDesugaredCommand cmd
isDesugaredCommand (Read _ cns) = isDesugaredTerm cns
isDesugaredCommand (Jump _ _) = True
isDesugaredCommand (ExitSuccess _) = True
isDesugaredCommand (ExitFailure _) = True
isDesugaredCommand (PrimOp _ _ _ subst) = and (isDesugaredPCTerm <$> subst)

---------------------------------------------------------------------------------
-- Desugar Terms
--
-- This translates terms into the core subset of terms.
---------------------------------------------------------------------------------

resVar :: FreeVarName
resVar = MkFreeVarName "$result"


desugarPCTerm :: PrdCnsTerm -> PrdCnsTerm
desugarPCTerm (PrdTerm tm) = PrdTerm $ desugarTerm tm
desugarPCTerm (CnsTerm tm) = CnsTerm $ desugarTerm tm

desugarTerm :: Term pc -> Term pc
desugarTerm (BoundVar loc pc annot idx) =
  BoundVar loc pc annot idx
desugarTerm (FreeVar loc pc annot fv) =
  FreeVar loc pc annot fv
desugarTerm (Xtor loc pc annot ns xt args) =
  Xtor loc pc annot ns xt (desugarPCTerm <$> args)
desugarTerm (MuAbs loc pc annot bs cmd) =
  MuAbs loc pc annot bs (desugarCmd cmd)
desugarTerm (XMatch loc pc annot ns cases) =
  XMatch loc pc annot ns (desugarCmdCase <$> cases)
desugarTerm (PrimLitI64 loc i) = PrimLitI64 loc i
desugarTerm (PrimLitF64 loc d) = PrimLitF64 loc d
-- we want to desugar e.D(args')
-- Mu k.[(desugar e) >> D (desugar <$> args')[k] ]
desugarTerm (Dtor loc _ _ ns xt t (args1,PrdRep,args2)) =
  let
    args = (desugarPCTerm <$> args1) ++ [CnsTerm $ FreeVar loc CnsRep Nothing resVar] ++ (desugarPCTerm <$> args2)
    cmd = Apply loc Nothing (desugarTerm t)
                           (Xtor loc CnsRep Nothing ns xt args)
  in
    MuAbs loc PrdRep Nothing Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd cmd
desugarTerm (Dtor loc _ _ ns xt t (args1,CnsRep,args2)) =
  let
    args = (desugarPCTerm <$> args1) ++ [PrdTerm $ FreeVar loc PrdRep Nothing resVar] ++ (desugarPCTerm <$> args2)
    cmd = Apply loc Nothing (desugarTerm t)
                           (Xtor loc CnsRep Nothing ns xt args)
  in
    MuAbs loc CnsRep Nothing Nothing $ commandClosing [(Prd, resVar)] $ shiftCmd cmd
-- we want to desugar match t { C (args) => e1 }
-- Mu k.[ (desugar t) >> match {C (args) => (desugar e1) >> k } ]
desugarTerm (Case loc _ ns t cases)   =
  let
    desugarMatchCase (MkTermCase _ xt args t) = MkCmdCase loc xt args  $ Apply loc Nothing (desugarTerm t) (FreeVar loc CnsRep Nothing resVar)
    cmd = Apply loc Nothing (desugarTerm t) (XMatch loc CnsRep Nothing ns  (desugarMatchCase <$> cases))
  in
    MuAbs loc PrdRep Nothing Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd cmd
-- we want to desugar comatch { D(args) => e }
-- comatch { D(args)[k] => (desugar e) >> k }
desugarTerm (Cocase loc _ ns cocases) =
  let
    desugarComatchCase (MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Cns,Nothing)] ++ as2 in
      MkCmdCase loc xt args $ Apply loc Nothing (desugarTerm t) (BoundVar loc CnsRep Nothing (0,length as1))
  in
    XMatch loc PrdRep Nothing ns $ desugarComatchCase <$> cocases

desugarCmdCase :: CmdCase -> CmdCase
desugarCmdCase (MkCmdCase loc xt args cmd) = MkCmdCase loc xt args (desugarCmd cmd)

desugarCmd :: Command -> Command
desugarCmd (Apply loc kind prd cns) = Apply loc kind (desugarTerm prd) (desugarTerm cns)
desugarCmd (Print loc prd cmd) = Print loc (desugarTerm prd) (desugarCmd cmd)
desugarCmd (Read loc cns) = Read loc (desugarTerm cns)
desugarCmd (Jump loc fv) = Jump loc fv
desugarCmd (ExitSuccess loc) = ExitSuccess loc
desugarCmd (ExitFailure loc) = ExitFailure loc
desugarCmd (PrimOp loc pt op subst) = PrimOp loc pt op (desugarPCTerm <$> subst)

---------------------------------------------------------------------------------
-- Translate Program
---------------------------------------------------------------------------------

desugarDecl :: Declaration -> Declaration
desugarDecl (PrdCnsDecl loc doc pc isRec fv annot tm) =
  PrdCnsDecl loc doc pc isRec fv annot (desugarTerm tm)
desugarDecl (CmdDecl loc doc fv cmd) =
  CmdDecl loc doc fv (desugarCmd cmd)
desugarDecl (DataDecl loc doc decl) =
  DataDecl loc doc decl
desugarDecl (XtorDecl loc doc dc xt args ret) =
  XtorDecl loc doc dc xt args ret
desugarDecl (ImportDecl loc doc mn) =
  ImportDecl loc doc mn
desugarDecl (SetDecl loc doc txt) =
  SetDecl loc doc txt
desugarDecl (TyOpDecl loc doc op prec assoc ty) =
  TyOpDecl loc doc op prec assoc ty

desugarProgram :: Program -> Program
desugarProgram ps = desugarDecl <$> ps

desugarEnvironment :: Environment -> Environment
desugarEnvironment (MkEnvironment { prdEnv, cnsEnv, cmdEnv, declEnv }) =
    MkEnvironment
      { prdEnv = (\(tm,loc,tys) -> (desugarTerm tm,loc,tys)) <$> prdEnv
      , cnsEnv = (\(tm,loc,tys) -> (desugarTerm tm,loc,tys)) <$> cnsEnv
      , cmdEnv = (\(cmd,loc) -> (desugarCmd cmd,loc)) <$> cmdEnv
      , declEnv = declEnv
      }