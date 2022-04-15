module Syntax.RST.Desugar where 
import Syntax.Common
import Utils
import Syntax.RST.Terms

resVar :: FreeVarName
resVar = MkFreeVarName "$result"

caseD :: Loc -> NominalStructural -> Term Prd -> [TermCase Prd] -> Term Prd
caseD loc ns tm cases = MuAbs loc PrdRep Nothing $ commandClosing [(Cns, resVar)] (shiftCmd cmd)
  where
    f :: TermCase Prd -> CmdCase
    f (MkTermCase loc xtor args t) = MkCmdCase loc xtor args (Apply loc t (FreeVar loc CnsRep resVar))
    cmd = Apply loc tm (XMatch loc CnsRep ns (map f cases))
    
-- we want to desugar e.D(args)
-- Mu k.[e >> D (args){k}
-- TODO: Not sure whether the code/signature is correct if e is a consumer
dtorD :: Loc -> PrdCnsRep pc -> NominalStructural ->  XtorName -> Term Prd -> SubstitutionI pc -> Term pc
dtorD loc CnsRep ns xt t (args1,CnsRep,args2) =  
  let
    args = args1 ++ [PrdTerm $ FreeVar loc PrdRep resVar] ++ args2
    cmd = Apply loc t (Xtor loc CnsRep ns xt args)
  in
    MuAbs loc CnsRep Nothing $ commandClosing [(Prd, resVar)] $ shiftCmd cmd
dtorD loc _ ns xt t (args1,PrdRep,args2) =  
  let
    args = args1 ++ [CnsTerm $ FreeVar loc CnsRep resVar] ++ args2
    cmd = Apply loc t (Xtor loc CnsRep ns xt args)
  in
    MuAbs loc PrdRep Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd cmd

cocaseD :: Loc -> NominalStructural -> [TermCaseI Prd] -> Term Prd
cocaseD loc ns cocases =  
  let
    desugarComatchCase (MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Cns,Nothing)] ++ as2 in
      MkCmdCase loc xt args $ Apply loc t (BoundVar loc CnsRep (0,length as1))
  in
    XMatch loc PrdRep ns $ desugarComatchCase <$> cocases
{-

ATTIC - saved for later

 sugar signatures

  Dtor :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural ->  XtorName -> Term Prd -> SubstitutionI pc -> Term pc

  CaseCnsPrdI :: Loc -> Typ Neg -> NominalStructural -> [TermCaseI Prd] -> Term Cns
  CaseCnsCnsI :: Loc -> Typ Neg -> NominalStructural -> [TermCaseI Cns] -> Term Cns

  -- | Left Elimination  :
  --
  -- foo(...,*,...) ; e
  --
  Semicolon :: Loc -> PrdCnsRep pc  -> Typ (PrdCnsToPol pc) -> NominalStructural -> XtorName -> SubstitutionI pc -> Term Cns -> Term pc

  -- | A copattern match:
  --
  -- cocase { ... }
  --
  CocasePrdI :: Loc -> Typ Pos -> NominalStructural -> [TermCaseI Prd] -> Term Prd
  CocaseCnsI :: Loc -> Typ Pos -> NominalStructural -> [TermCaseI Cns] -> Term Prd

  CocaseCns :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> Term Cns -> [TermCaseI pc] -> Term pc

  CasePrdCmd :: Loc -> NominalStructural -> Term Prd -> [CmdCase] -> Command
  CasePrdPrdI :: Loc -> NominalStructural -> Term Prd -> [TermCaseI Prd] -> Command
  CasePrdCnsI :: Loc -> NominalStructural -> Term Prd -> [TermCaseI Cns] -> Command
  CocaseCnsCmd :: Loc -> NominalStructural -> Term Cns -> [CmdCase] -> Command
  CocaseCnsPrdI :: Loc -> NominalStructural -> Term Cns -> [TermCaseI Prd] -> Command
  CocaseCnsCnsI :: Loc -> NominalStructural -> Term Cns -> [TermCaseI Cns] -> Command

desugarTerm (AST.CocaseCnsI loc _ ns cocases) =
  let
    desugarComatchCase (AST.MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Prd,Nothing)] ++ as2 in
      Core.MkCmdCase loc xt args $ Core.Apply loc Nothing (Core.BoundVar loc PrdRep (0,length as1)) (desugarTerm t)
  in
    Core.XMatch loc PrdRep ns $ desugarComatchCase <$> cocases

desugarTerm (AST.CaseCnsPrdI loc _ ns tmcasesI) =
  let
    desugarmatchCase (AST.MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Cns,Nothing)] ++ as2 in
      Core.MkCmdCase loc xt args $ Core.Apply loc Nothing (desugarTerm t) (Core.BoundVar loc CnsRep (0,length as1))
  in
    Core.XMatch loc CnsRep ns $ desugarmatchCase <$> tmcasesI
desugarTerm (AST.CaseCnsCnsI loc _ ns tmcasesI) =
  let
    desugarmatchCase (AST.MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Prd,Nothing)] ++ as2 in
      Core.MkCmdCase loc xt args $ Core.Apply loc Nothing (Core.BoundVar loc PrdRep (0,length as1)) (desugarTerm t)
  in
    Core.XMatch loc CnsRep ns $ desugarmatchCase <$> tmcasesI

  -- foo(...)[*](...) ; e
  -- desugares to mu k. foo(...)[k](...) >> e

desugarTerm (AST.Semicolon loc PrdRep _ ns xt (args1, PrdRep, args2) t) =
  let
    args = (desugarPCTerm <$> args1) ++ [Core.CnsTerm $ Core.FreeVar loc CnsRep resVar] ++ (desugarPCTerm <$> args2)
    cmd = Core.Apply loc Nothing  (Core.Xtor loc PrdRep ns xt args) (desugarTerm t)
  in
  Core.MuAbs loc PrdRep Nothing $ Core.commandClosing [(Cns, resVar)] $ Core.shiftCmd cmd

desugarTerm (AST.Semicolon loc CnsRep _ ns xt (args1, CnsRep, args2) t) =
  let
    args = (desugarPCTerm <$> args1) ++ [Core.PrdTerm $ Core.FreeVar loc PrdRep resVar] ++ (desugarPCTerm <$> args2)
    cmd = Core.Apply loc Nothing  (Core.Xtor loc PrdRep ns xt args) (desugarTerm t)
  in
  Core.MuAbs loc CnsRep Nothing $ Core.commandClosing [(Prd, resVar)] $ Core.shiftCmd cmd


desugarTerm (AST.CocaseCns loc PrdRep _ ns t tmcasesI) =
  let
    desugarComatchCase (AST.MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Prd,Nothing)] ++ as2 in
      Core.MkCmdCase loc xt args $ Core.Apply loc Nothing (desugarTerm t) (Core.BoundVar loc CnsRep (0,length as1))
    cmd = Core.Apply loc Nothing (Core.XMatch loc PrdRep ns  (desugarComatchCase <$> tmcasesI)) (desugarTerm t)
  in Core.MuAbs loc PrdRep Nothing $ Core.commandClosing [(Cns, resVar)] (Core.shiftCmd cmd)
desugarTerm (AST.CocaseCns loc CnsRep _ ns t tmcasesI) =
  let
    desugarComatchCase (AST.MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Prd,Nothing)] ++ as2 in
      Core.MkCmdCase loc xt args $ Core.Apply loc Nothing (Core.BoundVar loc PrdRep (0,length as1)) (desugarTerm t)
    cmd = Core.Apply loc Nothing (Core.XMatch loc PrdRep ns  (desugarComatchCase <$> tmcasesI)) (desugarTerm t)
  in Core.MuAbs loc CnsRep Nothing $ Core.commandClosing [(Prd, resVar)] (Core.shiftCmd cmd)


desugarCmdCase :: AST.CmdCase -> Core.CmdCase
desugarCmdCase (AST.MkCmdCase loc xt args cmd) =
  Core.MkCmdCase loc xt args (desugarCmd cmd)

desugarCmd :: AST.Command -> Core.Command
desugarCmd (AST.Apply loc kind prd cns) =
  Core.Apply loc kind (desugarTerm prd) (desugarTerm cns)
desugarCmd (AST.Print loc prd cmd) =
  Core.Print loc (desugarTerm prd) (desugarCmd cmd)
desugarCmd (AST.Read loc cns) =
  Core.Read loc (desugarTerm cns)
desugarCmd (AST.Jump loc fv) =
  Core.Jump loc fv
desugarCmd (AST.ExitSuccess loc) =
  Core.ExitSuccess loc
desugarCmd (AST.ExitFailure loc) =
  Core.ExitFailure loc
desugarCmd (AST.PrimOp loc pt op subst) =
  Core.PrimOp loc pt op (desugarPCTerm <$> subst)
-- case e of {cmd-cases} 
--    desugares to 
-- e >> case {cmd-cases}  
desugarCmd (AST.CasePrdCmd loc ns t cases) = Core.Apply loc Nothing (desugarTerm t) (Core.XMatch loc CnsRep ns (desugarCmdCase <$> cases))
desugarCmd (AST.CasePrdPrdI loc ns t cases) =
  let
    desugarmatchCase (AST.MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Cns,Nothing)] ++ as2 in
      Core.MkCmdCase loc xt args $ Core.Apply loc Nothing (desugarTerm t) (Core.BoundVar loc CnsRep (0,length as1))
  in
    Core.Apply loc Nothing (desugarTerm t) (Core.XMatch loc CnsRep ns $ desugarmatchCase <$> cases)
desugarCmd (AST.CasePrdCnsI loc ns t cases) =
  let
    desugarmatchCase (AST.MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Prd,Nothing)] ++ as2 in
      Core.MkCmdCase loc xt args $ Core.Apply loc Nothing (Core.BoundVar loc PrdRep (0,length as1)) (desugarTerm t)
  in
    Core.Apply loc Nothing (desugarTerm t) (Core.XMatch loc CnsRep ns $ desugarmatchCase <$> cases)

desugarCmd (AST.CocaseCnsCmd loc ns t cases) = Core.Apply loc Nothing (Core.XMatch loc PrdRep ns (desugarCmdCase <$> cases)) (desugarTerm t)
desugarCmd (AST.CocaseCnsPrdI loc ns t cases) =
  let
    desugarcomatchCase (AST.MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Cns,Nothing)] ++ as2 in
      Core.MkCmdCase loc xt args $ Core.Apply loc Nothing (desugarTerm t) (Core.BoundVar loc CnsRep (0,length as1))
  in
    Core.Apply loc Nothing (Core.XMatch loc PrdRep ns $ desugarcomatchCase <$> cases) (desugarTerm t)

desugarCmd (AST.CocaseCnsCnsI loc ns t cases) =
  let
    desugarcomatchCase (AST.MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Prd,Nothing)] ++ as2 in
      Core.MkCmdCase loc xt args $ Core.Apply loc Nothing (Core.BoundVar loc PrdRep (0,length as1)) (desugarTerm t)
  in
    Core.Apply loc Nothing (Core.XMatch loc PrdRep ns $ desugarcomatchCase <$> cases) (desugarTerm t)

-}    