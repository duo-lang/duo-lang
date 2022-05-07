module Sugar.AST
  where

import Syntax.AST.Terms
import Syntax.Common
import Utils
import Syntax.Common.Annot
import Syntax.RST.Types (flipType, Typ)
-- CaseOfCmd:
--   [[case e of { Ctor(xs) => cmd }]] = < [[e]] | case { Ctor(xs) => [[cmd]] } >
--   Annotations used on RHS: ApplyAnnotCaseOfCmd, MatchAnnotCaseOfCmd
pattern CaseOfCmd :: Loc -> NominalStructural -> Term Prd -> Typ Neg -> [CmdCase] -> Command
pattern CaseOfCmd loc  ns t ty cases <- Apply loc ApplyAnnotCaseOfCmd _ t (XCase _ MatchAnnotCaseOfCmd CnsRep ty ns cases)
 where
    CaseOfCmd loc ns t ty cases = Apply loc ApplyAnnotCaseOfCmd Nothing t (XCase loc MatchAnnotCaseOfCmd CnsRep ty ns cases)

-- CocaseOfCmd: 
--   [[cocase e of { Dtor(xs) => cmd }]] = < cocase { Dtor(xs) => [[cmd]] } | [[e]] >
--   Annotations used on RHS: ApplyAnnotCocaseOfCmd, MatchAnnotCocaseOfCmd

pattern CocaseOfCmd :: Loc -> NominalStructural -> Term Cns -> Typ Pos -> [CmdCase] -> Command
pattern CocaseOfCmd loc ns t ty cases <- Apply loc ApplyAnnotCocaseOfCmd Nothing (XCase _ MatchAnnotCocaseOfCmd PrdRep ty ns cases) t
 where
    CocaseOfCmd loc ns t ty cases = Apply loc ApplyAnnotCocaseOfCmd Nothing (XCase loc MatchAnnotCocaseOfCmd PrdRep ty  ns cases) t


mySplitAt :: Int -> [a] -> ([a],(), [a])
mySplitAt n x = (a, (), tail b)
  where (a,b) = splitAt n x

resugarCmdCase :: PrdCnsRep pc -> CmdCase -> TermCaseI pc
resugarCmdCase PrdRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotXCaseOfIInner i) Nothing t (BoundVar _ CnsRep _ (0,_)))) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase CnsRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotXCaseOfIInner i) Nothing (BoundVar _ PrdRep _ (0,_)) t)) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase _ cmd = error $ "cannot resugar " ++ show cmd

-- CaseOf:
--   [[case e of { Ctor(xs,*,ys) => prd }]] =
--      < [[e]] | case { Ctor(xs,k,ys) => < [[prd]] | k >} >
--         e : t+     case { Ctor(xs,k,ys) => < [[prd]] | k>  : t-
--                                                  prd : t'+  k : t'- }
--   [[case e of { Ctor(xs,*,ys) => cns }]] =
--      < [[e]] | case { Ctor(xs,k,ys) => < k | [[cns]] > } >
--   Annotations used on RHS: ApplyAnnotCaseOfIInner, ApplyAnnotCaseOfIOuter, MatchAnnotCaseOfI

pattern CaseOfI :: Loc -> PrdCnsRep pc -> NominalStructural -> Term Prd -> Typ Neg -> [TermCaseI pc] -> Command
pattern CaseOfI loc rep ns t ty cases <-
  Apply loc ApplyAnnotCaseOfIOuter Nothing t (XCase _ MatchAnnotCaseOfI (flipPrdCns -> rep) ty ns (map (resugarCmdCase rep) -> cases))
  where
    CaseOfI loc PrdRep ns t ty cases =
     let
       desugarmatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotXCaseOfIInner $ length as1) Nothing t (BoundVar loc CnsRep ty (0,length as1))
     in
       Apply loc ApplyAnnotCaseOfIOuter Nothing t (XCase loc MatchAnnotCaseOfI CnsRep ty ns $ desugarmatchCase <$> cases)
    CaseOfI loc CnsRep ns t ty cases =
     let
       desugarmatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotXCaseOfIInner $ length as1) Nothing  (BoundVar loc PrdRep ty (0,length as1)) t
     in
       Apply loc ApplyAnnotCaseOfIOuter Nothing t (XCase loc MatchAnnotCaseOfI CnsRep ty ns $ desugarmatchCase <$> cases)


-- CocaseOfI:
--   [[cocase e of { Dtor(xs,*,ys) => prd }]] =
--      < cocase { Dtor(xs,k,ys) => < [[prd]] | k > } | [[e]] >
--   [[cocase e of { Dtor(xs,*,ys) => cns }]] =
--      < cocase { Dtor(xs,k,ys) => < k | [[cns]] > } | [[e]] >
--   Annotations used on RHS: ApplyAnnotCaseOfIInner, ApplyAnnotCaseOfIOuter, MatchAnnotCaseOfI

pattern CocaseOfI :: Loc -> PrdCnsRep pc -> NominalStructural -> Term Cns -> [TermCaseI pc] -> Command
pattern CocaseOfI loc rep ns t cases <-
  Apply loc ApplyAnnotCocaseOfIOuter Nothing (XCase _ MatchAnnotCocaseOfI (flipPrdCns -> rep) _ ns (map (resugarCmdCase rep) -> cases)) t
  where
    CocaseOfI loc PrdRep ns t cases =
     let
       desugarcomatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotXCaseOfIInner $ length as1) Nothing t (BoundVar loc CnsRep (flipType (getTypeTerm t))  (0,length as1))
     in
       Apply loc ApplyAnnotCocaseOfIOuter Nothing (XCase loc MatchAnnotCocaseOfI PrdRep (flipType (getTypeTerm t)) ns $ desugarcomatchCase <$> cases) t
    CocaseOfI loc CnsRep ns t cases =
     let
       desugarcomatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotXCaseOfIInner $ length as1) Nothing  (BoundVar loc PrdRep (flipType (getTypeTerm t))  (0,length as1)) t
     in
       Apply loc ApplyAnnotCocaseOfIOuter Nothing (XCase loc MatchAnnotCocaseOfI PrdRep (flipType (getTypeTerm t))  ns $ desugarcomatchCase <$> cases) t


resugarSubst ::  PrdCnsRep pc -> Int -> Substitution -> SubstitutionI pc
resugarSubst rep n x = (a, rep, tail b)
  where (a,b) = splitAt n x

resVar :: FreeVarName
resVar = MkFreeVarName "$result"

-- Semi:
--   [[Ctor(as,*,bs) ;; e]] = mu k. <  Ctor([[as]],k,[[bs]])  |  [[e]]  >
--   Annotations used on RHS: MuAnnotSemi, ApplyAnnotSemi, XtorAnnotSemi
{-
pattern Semi :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) ->NominalStructural -> XtorName -> SubstitutionI pc -> Term Cns -> Term pc
pattern Semi loc rep ty ns xt substi t <-
    MuAbs loc MuAnnotSemi ty rep Nothing (shiftCmd ShiftDown -> Apply _ ApplyAnnotSemi Nothing (Xtor _ (XtorAnnotSemi i) PrdRep _ ns xt (resugarSubst rep i -> substi)) t)
    where 
        Semi loc PrdRep ty ns xt (args1, PrdRep, args2) t = 
            let
                args = args1 ++ [CnsTerm $ FreeVar loc CnsRep _ resVar] ++ args2
                cmd = Apply loc ApplyAnnotSemi Nothing  (Xtor loc (XtorAnnotSemi (length args1)) PrdRep _ ns xt args) t
            in
            MuAbs loc MuAnnotSemi  PrdRep ty Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd ShiftUp cmd
        Semi loc CnsRep ty ns xt (args1, CnsRep, args2) t =  
            let
                args = args1 ++ [PrdTerm $ FreeVar loc PrdRep (flipType (getTypeTerm t)) resVar] ++ args2
                cmd = Apply loc ApplyAnnotSemi Nothing  (Xtor loc (XtorAnnotSemi (length args1)) PrdRep _ ns xt args) t
            in
            MuAbs loc MuAnnotSemi CnsRep ty Nothing $ commandClosing [(Prd, resVar)] $ shiftCmd ShiftUp cmd
-}