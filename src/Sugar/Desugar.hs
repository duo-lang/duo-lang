module Sugar.Desugar
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
import Eval.Definition (EvalEnv)
import Syntax.AST.Program qualified as AST
import Syntax.AST.Terms qualified as AST
import Syntax.Core.Program qualified as Core
import Syntax.Core.Terms qualified as Core
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
isDesugaredTerm (AST.XCase _ _ _ _ cases) =
  and ((\AST.MkCmdCase { cmdcase_cmd } -> isDesugaredCommand cmdcase_cmd ) <$> cases)
isDesugaredTerm AST.PrimLitI64{} = True
isDesugaredTerm AST.PrimLitF64{} = True
-- Non-core terms
isDesugaredTerm AST.Dtor{} = False
isDesugaredTerm AST.CaseOf {} = False
isDesugaredTerm AST.CocaseOf {} = False
isDesugaredTerm AST.CaseI {} = False
isDesugaredTerm AST.CocaseI {} = False
isDesugaredTerm AST.Semi {} = False


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
isDesugaredCommand AST.CaseOfCmd {} =  False
isDesugaredCommand AST.CaseOfI {} =  False
isDesugaredCommand AST.CocaseOfCmd {} =  False
isDesugaredCommand AST.CocaseOfI {} =  False

---------------------------------------------------------------------------------
-- Desugar Terms
--
-- This translates terms into the core subset of terms.
---------------------------------------------------------------------------------

resVar :: FreeVarName
resVar = MkFreeVarName "$result"

desugarPCTerm :: AST.PrdCnsTerm -> Core.PrdCnsTerm
desugarPCTerm (AST.PrdTerm tm) = Core.PrdTerm $ desugarTerm tm
desugarPCTerm (AST.CnsTerm tm) = Core.CnsTerm $ desugarTerm tm

desugarPat :: AST.Pattern -> Core.Pattern
desugarPat (AST.XtorPat loc xt args) = Core.XtorPat loc xt args

desugarTerm :: AST.Term pc -> Core.Term pc
---------------------------------------------------------------------------------
-- Core constructs
---------------------------------------------------------------------------------
desugarTerm (AST.BoundVar loc pc _annot idx) =
  Core.BoundVar loc pc idx
desugarTerm (AST.FreeVar loc pc _annot fv) =
  Core.FreeVar loc pc fv
desugarTerm (AST.Xtor loc pc _annot ns xt args) =
  Core.Xtor loc Core.XtorAnnotOrig pc ns xt (desugarPCTerm <$> args)
desugarTerm (AST.MuAbs loc pc _annot bs cmd) =
  Core.MuAbs loc Core.MuAnnotOrig pc bs (desugarCmd cmd)
desugarTerm (AST.XCase loc pc _annot ns cases) =
  Core.XCase loc Core.MatchAnnotOrig pc ns (desugarCmdCase <$> cases)
---------------------------------------------------------------------------------
-- Syntactic sugar
--
-- Semi:
--   [[Ctor(as,*,bs) ;; e]] = mu k. <  Ctor([[as]],k,[[bs]])  |  [[e]]  >
--   Annotations used on RHS: MuAnnotSemi, ApplyAnnotSemi, XtorAnnotSemi
--
-- Dtor:
--   [[e.Dtor(as,*,bs)]]    = mu k. <  [[e]]  | Dtor([[as]], k, [[bs]])
--   Annotations used on RHS: MuAnnotDtor, ApplyAnnotDtor, XtorAnnotDtor
--
---------------------------------------------------------------------------------
desugarTerm (AST.Semi loc PrdRep _ ns xt (args1, PrdRep, args2) t) = 
  let
    args = (desugarPCTerm <$> args1) ++ [Core.CnsTerm $ Core.FreeVar loc CnsRep resVar] ++ (desugarPCTerm <$> args2)
    cmd = Core.Apply loc Core.ApplyAnnotSemi Nothing  (Core.Xtor loc Core.XtorAnnotSemi PrdRep ns xt args) (desugarTerm t)
  in
  Core.MuAbs loc Core.MuAnnotSemi PrdRep Nothing $ Core.commandClosing [(Cns, resVar)] $ Core.shiftCmd cmd
desugarTerm (AST.Semi loc CnsRep _ ns xt (args1, CnsRep, args2) t) = 
  let
    args = (desugarPCTerm <$> args1) ++ [Core.PrdTerm $ Core.FreeVar loc PrdRep resVar] ++ (desugarPCTerm <$> args2)
    cmd = Core.Apply loc Core.ApplyAnnotSemi Nothing  (Core.Xtor loc Core.XtorAnnotSemi PrdRep ns xt args) (desugarTerm t)
  in
  Core.MuAbs loc Core.MuAnnotSemi CnsRep Nothing $ Core.commandClosing [(Prd, resVar)] $ Core.shiftCmd cmd
desugarTerm (AST.Dtor loc _ _ ns xt t (args1,PrdRep,args2)) =
  let
    args = (desugarPCTerm <$> args1) ++ [Core.CnsTerm $ Core.FreeVar loc CnsRep resVar] ++ (desugarPCTerm <$> args2)
    cmd = Core.Apply loc Core.ApplyAnnotDtor Nothing (desugarTerm t)
                           (Core.Xtor loc Core.XtorAnnotDtor CnsRep ns xt args)
  in
    Core.MuAbs loc Core.MuAnnotDtor PrdRep Nothing $ Core.commandClosing [(Cns, resVar)] $ Core.shiftCmd cmd
desugarTerm (AST.Dtor loc _ _ ns xt t (args1,CnsRep,args2)) =
  let
    args = (desugarPCTerm <$> args1) ++ [Core.PrdTerm $ Core.FreeVar loc PrdRep resVar] ++ (desugarPCTerm <$> args2)
    cmd = Core.Apply loc Core.ApplyAnnotDtor Nothing (desugarTerm t)
                                (Core.Xtor loc Core.XtorAnnotDtor CnsRep ns xt args)
  in
    Core.MuAbs loc Core.MuAnnotDtor CnsRep Nothing $ Core.commandClosing [(Prd, resVar)] $ Core.shiftCmd cmd
---------------------------------------------------------------------------------
-- Syntactic sugar
-- 
-- CaseOf:
--  [[case e of { Ctor(xs) => prd }]] = mu k. < [[e]]  |  case { Ctor(xs) => < [[prd]]  |  k > }
--  [[case e of { Ctor(xs) => cns }]] = mu k. < [[e]]  |  case { Ctor(xs) => < k  | [[cns]] > }
--  Annotations used on RHS: MuAnnotCaseOf, ApplyAnnotCaseOfOuter, ApplyAnnotCaseOfInner, MatchAnnotCaseOf
--
-- CocaseOf:
--  [[cocase e of { Dtor(xs) => prd }]] = mu k. < cocase { Dtor(xs) => < [[prd]] | k > }  | [[e]] >
--  [[cocase e of { Dtor(xs) => cns }]] = mu k. < cocase { Dtor(xs) => < k  |  [[cns ]]}  | [[e]] >
--  Annotations used on RHS: MuAnnotCocaseOf, ApplyAnnotCocaseOfOuter, ApplyAnnotCocaseOfInner, MatchAnnotCocaseOf
--
---------------------------------------------------------------------------------
desugarTerm (AST.CaseOf loc PrdRep _ ns t cases) =
  let
    desugarMatchCase (AST.MkTermCase _ pat t) = Core.MkCmdCase loc (desugarPat pat)  $ Core.Apply loc Core.ApplyAnnotCaseOfInner Nothing (desugarTerm t) (Core.FreeVar loc CnsRep resVar)
    cmd = Core.Apply loc Core.ApplyAnnotCaseOfOuter Nothing (desugarTerm t) (Core.XCase loc Core.MatchAnnotCaseOf CnsRep ns  (desugarMatchCase <$> cases))
  in
    Core.MuAbs loc Core.MuAnnotCaseOf PrdRep Nothing $ Core.commandClosing [(Cns, resVar)] $ Core.shiftCmd cmd
desugarTerm (AST.CaseOf loc CnsRep _ ns t cases) =
  let
    desugarMatchCase (AST.MkTermCase _ pat t) = Core.MkCmdCase loc (desugarPat pat)  $ Core.Apply loc Core.ApplyAnnotCaseOfInner Nothing (Core.FreeVar loc PrdRep  resVar) (desugarTerm t)
    cmd = Core.Apply loc Core.ApplyAnnotCaseOfOuter Nothing (desugarTerm t) (Core.XCase loc Core.MatchAnnotCaseOf CnsRep ns  (desugarMatchCase <$> cases))
  in
    Core.MuAbs loc Core.MuAnnotCaseOf CnsRep Nothing $ Core.commandClosing [(Cns, resVar)] $ Core.shiftCmd cmd
desugarTerm (AST.CocaseOf loc PrdRep _ ns t cases) =
  let
     desugarComatchCase (AST.MkTermCase _ pat t) = Core.MkCmdCase loc (desugarPat pat) $ Core.Apply loc Core.ApplyAnnotCocaseOfInner Nothing (desugarTerm t) (Core.FreeVar loc CnsRep resVar)
     cmd = Core.Apply loc Core.ApplyAnnotCocaseOfOuter Nothing (Core.XCase loc Core.MatchAnnotCocaseOf PrdRep ns  (desugarComatchCase <$> cases)) (desugarTerm t)
  in Core.MuAbs loc Core.MuAnnotCocaseOf PrdRep Nothing $ Core.commandClosing [(Cns, resVar)] $ Core.shiftCmd cmd
desugarTerm (AST.CocaseOf loc CnsRep _ ns t cases) =
  let
    desugarComatchCase (AST.MkTermCase _ pat t) = Core.MkCmdCase loc (desugarPat pat) $ Core.Apply loc Core.ApplyAnnotCocaseOfInner Nothing (Core.FreeVar loc PrdRep resVar) (desugarTerm t)
    cmd = Core.Apply loc Core.ApplyAnnotCocaseOfOuter Nothing (Core.XCase loc Core.MatchAnnotCocaseOf PrdRep ns  (desugarComatchCase <$> cases)) (desugarTerm t)
  in Core.MuAbs loc Core.MuAnnotCocaseOf CnsRep Nothing $ Core.commandClosing [(Prd, resVar)] (Core.shiftCmd cmd)
---------------------------------------------------------------------------------
-- Syntactic sugar
--
-- CaseI:
--   [[case { Ctor(xs,*,ys) => prd }]] = case { Ctor(xs,k,ys) => < [[prd]] | k > }
--   [[case { Ctor(xs,*,ys) => cns }]] = case { Ctor(xs,k,ys) => < k | [[cns]] > }
--   Annotations used on RHS: MatchAnnotCaseI, ApplyAnnotCaseI
--
-- CocaseI:
--   [[cocase { Dtor(xs,*,ys) => prd }]] = cocase { Dtor(xs,k,ys) => < [[prd]] | k > }
--   [[cocase { Dtor(xs,*,ys) => cns }]] = cocase { Dtor(xs,k,ys) => < k | [[cns]] > }
--   Annotations used on RHS: MatchAnnotCocaseI, ApplyAnnotCocaseI
--
---------------------------------------------------------------------------------
desugarTerm (AST.CaseI loc PrdRep _ ns tmcasesI) = 
  let
    desugarmatchCase (AST.MkTermCaseI _ (AST.XtorPatI loc xt (as1, (), as2)) t) =
      let pat = Core.XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2) in
      Core.MkCmdCase loc pat $ Core.Apply loc Core.ApplyAnnotCaseI Nothing (desugarTerm t) (Core.BoundVar loc CnsRep (0,length as1))
  in
    Core.XCase loc Core.MatchAnnotCaseI CnsRep ns $ desugarmatchCase <$> tmcasesI
desugarTerm (AST.CaseI loc CnsRep _ ns tmcasesI) = 
  let
    desugarmatchCase (AST.MkTermCaseI _ (AST.XtorPatI loc xt (as1, (), as2)) t) =
      let pat = Core.XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2) in
      Core.MkCmdCase loc pat $ Core.Apply loc Core.ApplyAnnotCaseI Nothing (Core.BoundVar loc PrdRep (0,length as1)) (desugarTerm t)
  in
    Core.XCase loc Core.MatchAnnotCaseI CnsRep ns $ desugarmatchCase <$> tmcasesI
desugarTerm (AST.CocaseI loc PrdRep _ ns cocases) =
  let
    desugarComatchCase (AST.MkTermCaseI _ (AST.XtorPatI loc xt (as1, (), as2)) t) =
      let pat = Core.XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2) in
      Core.MkCmdCase loc pat $ Core.Apply loc Core.ApplyAnnotCocaseI Nothing (desugarTerm t) (Core.BoundVar loc CnsRep (0,length as1))
  in
    Core.XCase loc Core.MatchAnnotCocaseI PrdRep ns $ desugarComatchCase <$> cocases
desugarTerm (AST.CocaseI loc CnsRep _ ns cocases) =
  let
    desugarComatchCase (AST.MkTermCaseI _ (AST.XtorPatI loc xt (as1, (), as2)) t) =
      let pat = Core.XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2) in
      Core.MkCmdCase loc pat $ Core.Apply loc Core.ApplyAnnotCocaseI Nothing (Core.BoundVar loc PrdRep (0,length as1)) (desugarTerm t)
  in
    Core.XCase loc Core.MatchAnnotCocaseI PrdRep ns $ desugarComatchCase <$> cocases
---------------------------------------------------------------------------------
-- Primitive constructs
---------------------------------------------------------------------------------
desugarTerm (AST.PrimLitI64 loc i) =
  Core.PrimLitI64 loc i
desugarTerm (AST.PrimLitF64 loc d) =
  Core.PrimLitF64 loc d

desugarCmdCase :: AST.CmdCase -> Core.CmdCase
desugarCmdCase (AST.MkCmdCase loc pat cmd) =
  Core.MkCmdCase loc (desugarPat pat) (desugarCmd cmd)

desugarCmd :: AST.Command -> Core.Command
desugarCmd (AST.Apply loc kind prd cns) =
  Core.Apply loc Core.ApplyAnnotOrig kind (desugarTerm prd) (desugarTerm cns)
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
---------------------------------------------------------------------------------
-- Syntactic sugar
--
-- CaseOfCmd:
--   [[case e of { Ctor(xs) => cmd }]] = < [[e]] | case { Ctor(xs) => [[cmd]] } >
--   Annotations used on RHS: ApplyAnnotCaseOfCmd, MatchAnnotCaseOfCmd
--
-- CocaseOfCmd:
--   [[cocase e of { Dtor(xs) => cmd }]] = < cocase { Dtor(xs) => [[cmd]] } | [[e]] >
--   Annotations used on RHS: ApplyAnnotCocaseOfCmd, MatchAnnotCocaseOfCmd
--
---------------------------------------------------------------------------------
desugarCmd (AST.CaseOfCmd loc ns t cases) =
  Core.Apply loc Core.ApplyAnnotCaseOfCmd Nothing (desugarTerm t) (Core.XCase loc Core.MatchAnnotCaseOfCmd CnsRep ns (desugarCmdCase <$> cases))
desugarCmd (AST.CocaseOfCmd loc ns t cases) =
  Core.Apply loc Core.ApplyAnnotCocaseOfCmd Nothing (Core.XCase loc Core.MatchAnnotCocaseOfCmd PrdRep ns (desugarCmdCase <$> cases)) (desugarTerm t)
---------------------------------------------------------------------------------
-- Syntactic sugar
--
-- CaseOfI:
--   [[case e of { Ctor(xs,*,ys) => prd }]] =
--      < [[e]] | case { Ctor(xs,k,ys) => < [[prd]] | k >} >
--   [[case e of { Ctor(xs,*,ys) => cns }]] =
--      < [[e]] | case { Ctor(xs,k,ys) => < k | [[cns]] > } >
--   Annotations used on RHS: ApplyAnnotCaseOfIInner, ApplyAnnotCaseOfIOuter, MatchAnnotCaseOfI
--
-- CocaseOfI:
--   [[cocase e of { Dtor(xs,*,ys) => prd }]] =
--      < cocase { Dtor(xs,k,ys) => < [[prd]] | k > } | [[e]] >
--   [[cocase e of { Dtor(xs,*,ys) => cns }]] =
--      < cocase { Dtor(xs,k,ys) => < k | [[cns]] > } | [[e]] >
--   Annotations used on RHS: ApplyAnnotCocaseOfIInner, ApplyAnnotCocaseOfIOuter, MatchAnnotCocaseOfI
--
---------------------------------------------------------------------------------
desugarCmd (AST.CaseOfI loc PrdRep ns t cases) = 
  let
    desugarmatchCase (AST.MkTermCaseI _ (AST.XtorPatI loc xt (as1, (), as2)) t) =
      let pat = (Core.XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2))  in
      Core.MkCmdCase loc pat $ Core.Apply loc (Core.ApplyAnnotCaseOfIInner $ length as1) Nothing (desugarTerm t) (Core.BoundVar loc CnsRep (0,length as1))
  in
    Core.Apply loc Core.ApplyAnnotCaseOfIOuter Nothing (desugarTerm t) (Core.XCase loc Core.MatchAnnotCaseOfI CnsRep ns $ desugarmatchCase <$> cases)
desugarCmd (AST.CaseOfI loc CnsRep ns t cases) = 
  let
    desugarmatchCase (AST.MkTermCaseI _ (AST.XtorPatI loc xt (as1, (), as2)) t) =
      let pat = Core.XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2) in
      Core.MkCmdCase loc pat $ Core.Apply loc (Core.ApplyAnnotCaseOfIInner $ length as1) Nothing (Core.BoundVar loc PrdRep (0,length as1)) (desugarTerm t) 
  in
    Core.Apply loc Core.ApplyAnnotCaseOfIOuter Nothing (desugarTerm t) (Core.XCase loc Core.MatchAnnotCaseOfI CnsRep ns $ desugarmatchCase <$> cases)
desugarCmd (AST.CocaseOfI loc PrdRep ns t cases) = 
  let
    desugarcomatchCase (AST.MkTermCaseI _ (AST.XtorPatI loc xt (as1, (), as2)) t) =
      let pat = Core.XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2) in
      Core.MkCmdCase loc pat $ Core.Apply loc (Core.ApplyAnnotCocaseOfIInner $ length as1) Nothing (desugarTerm t) (Core.BoundVar loc CnsRep (0,length as1))  
  in
    Core.Apply loc Core.ApplyAnnotCocaseOfIOuter Nothing (Core.XCase loc Core.MatchAnnotCocaseOfI PrdRep ns $ desugarcomatchCase <$> cases) (desugarTerm t)
desugarCmd (AST.CocaseOfI loc CnsRep ns t cases) = 
  let
    desugarcomatchCase (AST.MkTermCaseI _ (AST.XtorPatI loc xt (as1, (), as2)) t) =
      let pat = Core.XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2) in
      Core.MkCmdCase loc pat $ Core.Apply loc (Core.ApplyAnnotCocaseOfIInner $ length as1) Nothing (Core.BoundVar loc PrdRep (0,length as1)) (desugarTerm t)  
  in
    Core.Apply loc Core.ApplyAnnotCocaseOfIOuter Nothing (Core.XCase loc Core.MatchAnnotCocaseOfI PrdRep ns $ desugarcomatchCase <$> cases) (desugarTerm t)

---------------------------------------------------------------------------------
-- Translate Program
---------------------------------------------------------------------------------

desugarDecl :: AST.Declaration -> Core.Declaration
desugarDecl (AST.PrdCnsDecl loc doc pc isRec fv annot tm) =
  Core.PrdCnsDecl loc doc pc isRec fv annot (desugarTerm tm)
desugarDecl (AST.CmdDecl loc doc fv cmd) =
  Core.CmdDecl loc doc fv (desugarCmd cmd)
desugarDecl (AST.DataDecl loc doc decl) =
  Core.DataDecl loc doc decl
desugarDecl (AST.XtorDecl loc doc dc xt args ret) =
  Core.XtorDecl loc doc dc xt args ret
desugarDecl (AST.ImportDecl loc doc mn) =
  Core.ImportDecl loc doc mn
desugarDecl (AST.SetDecl loc doc txt) =
  Core.SetDecl loc doc txt
desugarDecl (AST.TyOpDecl loc doc op prec assoc ty) =
  Core.TyOpDecl loc doc op prec assoc ty
desugarDecl (AST.TySynDecl loc doc nm ty) = 
  Core.TySynDecl loc doc nm ty

desugarProgram :: AST.Program -> Core.Program
desugarProgram ps = desugarDecl <$> ps

desugarEnvironment :: Environment -> EvalEnv
desugarEnvironment (MkEnvironment { prdEnv, cnsEnv, cmdEnv }) = (prd,cns,cmd)
  where
    prd = (\(tm,_,_) -> (desugarTerm tm)) <$> prdEnv
    cns = (\(tm,_,_) -> (desugarTerm tm)) <$> cnsEnv
    cmd = (\(cmd,_) -> (desugarCmd cmd)) <$> cmdEnv
