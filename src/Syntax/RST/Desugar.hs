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

desugarTerm (AST.CocasePrdI loc _ ns cocases) =
  let
    desugarComatchCase (AST.MkTermCaseI _ xt (as1, (), as2) t) =
      let args = as1 ++ [(Cns,Nothing)] ++ as2 in
      Core.MkCmdCase loc xt args $ Core.Apply loc Nothing (desugarTerm t) (Core.BoundVar loc CnsRep (0,length as1))
  in
    Core.XMatch loc PrdRep ns $ desugarComatchCase <$> cocases

desugarTerm (AST.Dtor loc _ _ ns xt t (args1,PrdRep,args2)) =
undefined
desugarTerm (AST.Dtor loc _ _ ns xt t (args1,CnsRep,args2)) =
  let
    args = (desugarPCTerm <$> args1) ++ [Core.PrdTerm $ Core.FreeVar loc PrdRep resVar] ++ (desugarPCTerm <$> args2)
    cmd = Core.Apply loc Nothing (desugarTerm t)
                                (Core.Xtor loc CnsRep ns xt args)
  in
    Core.MuAbs loc CnsRep Nothing $ Core.commandClosing [(Prd, resVar)] $ Core.shiftCmd cmd

-}    