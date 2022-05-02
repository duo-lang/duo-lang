module Sugar.Core
  where

import Syntax.Core.Program
import Syntax.Core.Terms
import Syntax.Common
import Utils
import Syntax.AST.Terms (ShiftDirection(..))

-- CaseOfCmd:
--   [[case e of { Ctor(xs) => cmd }]] = < [[e]] | case { Ctor(xs) => [[cmd]] } >
--   Annotations used on RHS: ApplyAnnotCaseOfCmd, MatchAnnotCaseOfCmd

pattern CaseOfCmd :: Loc -> NominalStructural -> Term Prd -> [CmdCase] -> Command
pattern CaseOfCmd loc ns t cases <- Apply loc ApplyAnnotCaseOfCmd Nothing t (XCase _ MatchAnnotCaseOfCmd CnsRep ns cases)
 where
    CaseOfCmd loc ns t cases = Apply loc ApplyAnnotCaseOfCmd Nothing t (XCase loc MatchAnnotCaseOfCmd CnsRep ns cases)

-- CocaseOfCmd:
--   [[cocase e of { Dtor(xs) => cmd }]] = < cocase { Dtor(xs) => [[cmd]] } | [[e]] >
--   Annotations used on RHS: ApplyAnnotCocaseOfCmd, MatchAnnotCocaseOfCmd

pattern CocaseOfCmd :: Loc -> NominalStructural -> Term Cns -> [CmdCase] -> Command
pattern CocaseOfCmd loc ns t cases <- Apply loc ApplyAnnotCocaseOfCmd Nothing (XCase _ MatchAnnotCocaseOfCmd PrdRep ns cases) t
 where
    CocaseOfCmd loc ns t cases = Apply loc ApplyAnnotCocaseOfCmd Nothing (XCase loc MatchAnnotCocaseOfCmd PrdRep ns cases) t

mySplitAt :: Int -> [a] -> ([a],(), [a])
mySplitAt n x = (a, (), tail b)
  where (a,b) = splitAt n x

data PatternI where
  XtorPatI :: Loc -> XtorName -> ([(PrdCns, Maybe FreeVarName)], (), [(PrdCns, Maybe FreeVarName)]) -> PatternI

data TermCaseI (pc :: PrdCns) = MkTermCaseI
  { tmcasei_loc  :: Loc
  , tmcasei_pat :: PatternI
  , tmcasei_term :: Term pc
  }
resugarCmdCase :: PrdCnsRep pc -> CmdCase -> TermCaseI pc
resugarCmdCase PrdRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotCaseOfIInner i) Nothing t (BoundVar _ CnsRep (0,_)))) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase CnsRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotCaseOfIInner i) Nothing (BoundVar _ PrdRep (0,_)) t)) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase _ cmd = error $ "cannot resugar " ++ show cmd


-- CaseOf:
--   [[case e of { Ctor(xs,*,ys) => prd }]] =
--      < [[e]] | case { Ctor(xs,k,ys) => < [[prd]] | k >} >
--   [[case e of { Ctor(xs,*,ys) => cns }]] =
--      < [[e]] | case { Ctor(xs,k,ys) => < k | [[cns]] > } >
--   Annotations used on RHS: ApplyAnnotCaseOfIInner, ApplyAnnotCaseOfIOuter, MatchAnnotCaseOfI

pattern CaseOfI :: Loc -> PrdCnsRep pc -> NominalStructural -> Term Prd -> [TermCaseI pc] -> Command
pattern CaseOfI loc rep ns t cases <-
  Apply loc ApplyAnnotCaseOfIOuter Nothing t (XCase _ MatchAnnotCaseOfI (flipPrdCns -> rep) ns (map (resugarCmdCase rep) -> cases))
  where
    CaseOfI loc PrdRep ns t cases =
     let
       desugarmatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotCaseOfIInner $ length as1) Nothing t (BoundVar loc CnsRep (0,length as1))
     in
       Apply loc ApplyAnnotCaseOfIOuter Nothing t (XCase loc MatchAnnotCaseOfI CnsRep ns $ desugarmatchCase <$> cases)
    CaseOfI loc CnsRep ns t cases =
     let
       desugarmatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotCaseOfIInner $ length as1) Nothing  (BoundVar loc PrdRep (0,length as1)) t
     in
       Apply loc ApplyAnnotCaseOfIOuter Nothing t (XCase loc MatchAnnotCaseOfI CnsRep ns $ desugarmatchCase <$> cases)


resugarCmdCocase :: PrdCnsRep pc -> CmdCase -> TermCaseI pc
resugarCmdCocase PrdRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotCocaseOfIInner i) Nothing t (BoundVar _ CnsRep (0,_)))) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCocase CnsRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotCocaseOfIInner i) Nothing (BoundVar _ PrdRep (0,_)) t)) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCocase _ cmd = error $ "cannot resugar " ++ show cmd

-- CocaseOfI:
--   [[cocase e of { Dtor(xs,*,ys) => prd }]] =
--      < cocase { Dtor(xs,k,ys) => < [[prd]] | k > } | [[e]] >
--   [[cocase e of { Dtor(xs,*,ys) => cns }]] =
--      < cocase { Dtor(xs,k,ys) => < k | [[cns]] > } | [[e]] >
--   Annotations used on RHS: ApplyAnnotCaseOfIInner, ApplyAnnotCaseOfIOuter, MatchAnnotCaseOfI

pattern CocaseOfI :: Loc -> PrdCnsRep pc -> NominalStructural -> Term Cns -> [TermCaseI pc] -> Command
pattern CocaseOfI loc rep ns t cases <-
  Apply loc ApplyAnnotCocaseOfIOuter Nothing (XCase _ MatchAnnotCocaseOfI (flipPrdCns -> rep) ns (map (resugarCmdCocase rep) -> cases)) t
  where
    CocaseOfI loc PrdRep ns t cases =
     let
       desugarcomatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotCocaseOfIInner $ length as1) Nothing t (BoundVar loc CnsRep (0,length as1))
     in
       Apply loc ApplyAnnotCocaseOfIOuter Nothing (XCase loc MatchAnnotCocaseOfI PrdRep ns $ desugarcomatchCase <$> cases) t
    CocaseOfI loc CnsRep ns t cases =
     let
       desugarcomatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotCocaseOfIInner $ length as1) Nothing  (BoundVar loc PrdRep (0,length as1)) t
     in
       Apply loc ApplyAnnotCocaseOfIOuter Nothing (XCase loc MatchAnnotCocaseOfI PrdRep ns $ desugarcomatchCase <$> cases) t


type SubstitutionI (pc :: PrdCns) = (Substitution, PrdCnsRep pc, Substitution)

resugarSubst ::  PrdCnsRep pc -> Int -> Substitution -> SubstitutionI pc
resugarSubst rep n x = (a, rep, tail b)
  where (a,b) = splitAt n x

resVar :: FreeVarName
resVar = MkFreeVarName "$result"

-- Semi:
--   [[Ctor(as,*,bs) ;; e]] = mu k. <  Ctor([[as]],k,[[bs]])  |  [[e]]  >
--   Annotations used on RHS: MuAnnotSemi, ApplyAnnotSemi, XtorAnnotSemi

pattern Semi :: Loc -> PrdCnsRep pc -> NominalStructural -> XtorName -> SubstitutionI pc -> Term Cns -> Term pc
pattern Semi loc rep ns xt substi t <-
    MuAbs loc MuAnnotSemi rep Nothing (shiftCmd ShiftDown -> Apply _ ApplyAnnotSemi Nothing (Xtor _ (XtorAnnotSemi i) PrdRep ns xt (resugarSubst rep i -> substi)) t)
    where 
        Semi loc PrdRep ns xt (args1, PrdRep, args2) t = 
            let
                args = args1 ++ [CnsTerm $ FreeVar loc CnsRep resVar] ++ args2
                cmd = Apply loc ApplyAnnotSemi Nothing  (Xtor loc (XtorAnnotSemi (length args1)) PrdRep ns xt args) t
            in
            MuAbs loc MuAnnotSemi PrdRep Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd ShiftUp cmd
        Semi loc CnsRep ns xt (args1, CnsRep, args2) t =  
            let
                args = args1 ++ [PrdTerm $ FreeVar loc PrdRep resVar] ++ args2
                cmd = Apply loc ApplyAnnotSemi Nothing  (Xtor loc (XtorAnnotSemi (length args1)) PrdRep ns xt args) t
            in
            MuAbs loc MuAnnotSemi CnsRep Nothing $ commandClosing [(Prd, resVar)] $ shiftCmd ShiftUp cmd
