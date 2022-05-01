module Sugar.Core
  where

import Syntax.Core.Program
import Syntax.Core.Terms
import Syntax.Common
import Utils

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

pattern CoCaseOfCmd :: Loc -> NominalStructural -> Term Cns -> [CmdCase] -> Command
pattern CoCaseOfCmd loc ns t cases <- Apply loc ApplyAnnotCocaseOfCmd Nothing (XCase _ MatchAnnotCocaseOfCmd PrdRep ns cases) t
 where
    CoCaseOfCmd loc ns t cases = Apply loc ApplyAnnotCocaseOfCmd Nothing (XCase loc MatchAnnotCocaseOfCmd PrdRep ns cases) t

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


-- CaseOfIPrd:
--   [[case e of { Ctor(xs,*,ys) => prd }]] =
--      < [[e]] | case { Ctor(xs,k,ys) => < [[prd]] | k >} >

pattern CaseOfIPrd :: Loc -> NominalStructural -> Term Prd -> [TermCaseI Prd] -> Command
pattern CaseOfIPrd loc ns t cases <-
  Apply loc ApplyAnnotCaseOfIOuter Nothing t (XCase _ MatchAnnotCaseOfI CnsRep ns (map (resugarCmdCase PrdRep) -> cases))
  where
    CaseOfIPrd loc ns t cases =
     let
       desugarmatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotCaseOfIInner $ length as1) Nothing t (BoundVar loc CnsRep (0,length as1))
     in
       Apply loc ApplyAnnotCaseOfIOuter Nothing t (XCase loc MatchAnnotCaseOfI CnsRep ns $ desugarmatchCase <$> cases)

-- CaseOfICns:
--   [[case e of { Ctor(xs,*,ys) => cns }]] =
--      < [[e]] | case { Ctor(xs,k,ys) => < k | [[cns]] > } >

pattern CaseOfICns :: Loc -> NominalStructural -> Term Prd -> [TermCaseI Cns] -> Command
pattern CaseOfICns loc ns t cases <-
  Apply loc ApplyAnnotCaseOfIOuter Nothing t (XCase _ MatchAnnotCaseOfI CnsRep ns (map (resugarCmdCase CnsRep) -> cases))
  where
    CaseOfICns loc ns t cases =
     let
       desugarmatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotCaseOfIInner $ length as1) Nothing  (BoundVar loc PrdRep (0,length as1)) t
     in
       Apply loc ApplyAnnotCaseOfIOuter Nothing t (XCase loc MatchAnnotCaseOfI CnsRep ns $ desugarmatchCase <$> cases)
