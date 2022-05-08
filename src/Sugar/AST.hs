module Sugar.CorASTe
  where

import Syntax.AST.Terms
import Syntax.Common
import Utils
import Syntax.Common.TypesPol

-- CaseOfCmd:
--   [[case e of { Ctor(xs) => cmd }]] = < [[e]] | case { Ctor(xs) => [[cmd]] } >
--   Annotations used on RHS: ApplyAnnotCaseOfCmd, MatchAnnotCaseOfCmd

pattern CaseOfCmd :: Loc -> NominalStructural -> Term Prd -> [CmdCase] -> Command
pattern CaseOfCmd loc ns t cases <- Apply loc ApplyAnnotCaseOfCmd _ t (XCase _ MatchAnnotCaseOfCmd CnsRep _ ns cases)

-- CocaseOfCmd:
--   [[cocase e of { Dtor(xs) => cmd }]] = < cocase { Dtor(xs) => [[cmd]] } | [[e]] >
--   Annotations used on RHS: ApplyAnnotCocaseOfCmd, MatchAnnotCocaseOfCmd

pattern CocaseOfCmd :: Loc -> NominalStructural -> Term Cns -> [CmdCase] -> Command
pattern CocaseOfCmd loc ns t cases <- Apply loc ApplyAnnotCocaseOfCmd _ (XCase _ MatchAnnotCocaseOfCmd PrdRep _ ns cases) t


mySplitAt :: Int -> [a] -> ([a],(), [a])
mySplitAt n x = (a, (), tail b)
  where (a,b) = splitAt n x

data PatternI where
  XtorPatI :: Loc -> XtorName -> ([(PrdCns, Maybe FreeVarName)], (), [(PrdCns, Maybe FreeVarName)]) -> PatternI

deriving instance Show PatternI

data TermCaseI (pc :: PrdCns) = MkTermCaseI
  { tmcasei_loc  :: Loc
  , tmcasei_pat :: PatternI
  , tmcasei_term :: Term pc
  }

resugarCmdCase :: PrdCnsRep pc -> CmdCase -> TermCaseI pc
resugarCmdCase PrdRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotXCaseOfIInner i) _ t (BoundVar _ CnsRep _ (0,_) ))) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase CnsRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotXCaseOfIInner i) _ (BoundVar _ PrdRep _ (0,_)) t)) =
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
  Apply loc ApplyAnnotCaseOfIOuter _ t (XCase _ MatchAnnotCaseOfI (flipPrdCns -> rep) _ ns (map (resugarCmdCase rep) -> cases))


-- CocaseOfI:
--   [[cocase e of { Dtor(xs,*,ys) => prd }]] =
--      < cocase { Dtor(xs,k,ys) => < [[prd]] | k > } | [[e]] >
--   [[cocase e of { Dtor(xs,*,ys) => cns }]] =
--      < cocase { Dtor(xs,k,ys) => < k | [[cns]] > } | [[e]] >
--   Annotations used on RHS: ApplyAnnotCaseOfIInner, ApplyAnnotCaseOfIOuter, MatchAnnotCaseOfI

pattern CocaseOfI :: Loc -> PrdCnsRep pc -> NominalStructural -> Term Cns -> [TermCaseI pc] -> Command
pattern CocaseOfI loc rep ns t cases <-
  Apply loc ApplyAnnotCocaseOfIOuter _ (XCase _ MatchAnnotCocaseOfI (flipPrdCns -> rep) _ ns (map (resugarCmdCase rep) -> cases)) t

-- | A SubstitutionI is like a substitution where one of the arguments has been
-- replaced by an implicit argument. The following convention for the use of the
-- `pc` parameter is used:
--
-- SubstitutionI Prd = ... [*] ...
-- SubstitutionI Cns = ... (*) ...

type SubstitutionI (pc :: PrdCns) = (Substitution, PrdCnsRep pc, Substitution)

resugarSubst ::  PrdCnsRep pc -> Int -> Substitution -> SubstitutionI pc
resugarSubst rep n x = (a, rep, tail b)
  where (a,b) = splitAt n x

-- Semi:
--   [[Ctor(as,*,bs) ;; e]] = mu k. <  Ctor([[as]],k,[[bs]])  |  [[e]]  >
--   Annotations used on RHS: MuAnnotSemi, ApplyAnnotSemi, XtorAnnotSemi

pattern Semi :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> XtorName -> SubstitutionI pc -> Term Cns -> Term pc
pattern Semi loc rep ty ns xt substi t <-
    MuAbs loc MuAnnotSemi rep ty Nothing (shiftCmd ShiftDown -> Apply _ ApplyAnnotSemi _ (Xtor _ (XtorAnnotSemi i) PrdRep _ ns xt (resugarSubst rep i -> substi)) t)

-- Dtor:
--   [[e.Dtor(as,*,bs)]]    = mu k. <  [[e]]  | Dtor([[as]], k, [[bs]])
--   Annotations used on RHS: MuAnnotDtor, ApplyAnnotDtor, XtorAnnotDtor

pattern Dtor :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> XtorName -> Term Prd -> SubstitutionI pc -> Term pc
pattern Dtor loc rep ty ns xt t substi <-
    MuAbs loc MuAnnotSemi rep ty Nothing (shiftCmd ShiftDown -> Apply _ ApplyAnnotSemi _ t (Xtor _ (XtorAnnotSemi i) CnsRep _ ns xt (resugarSubst rep i -> substi)) )

-- | Represents one case in a pattern match or copattern match.
--
--        X(x_1,...,x_n) => e
--        ^ ^^^^^^^^^^^     ^
--        |      |          |
--        |  tmcase_args  tmcase_term
--        |
--    tmcase_name
--

data TermCase (pc :: PrdCns) = MkTermCase
  { tmcase_loc  :: Loc
  , tmcase_pat :: Pattern
  , tmcase_term :: Term pc
  }        

resugarTermCase :: PrdCnsRep pc -> CmdCase -> TermCase pc
resugarTermCase PrdRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ _ _ t (FreeVar _ CnsRep _ _))) =
                     MkTermCase loc (XtorPat loc xt cases) t
resugarTermCase CnsRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ _ _ (FreeVar _ PrdRep _ _ ) t)) =
                     MkTermCase loc (XtorPat loc xt cases) t    
resugarTermCase _ cmd = error $ "compiler bug: resugarTermCase : cannot resugar " ++ show cmd                                  

-- CaseOf:
--  [[case e of { Ctor(xs) => prd }]] = mu k. < [[e]]  |  case { Ctor(xs) => < [[prd]]  |  k > }
--  [[case e of { Ctor(xs) => cns }]] = mu k. < [[e]]  |  case { Ctor(xs) => < k  | [[cns]] > }
--  Annotations used on RHS: MuAnnotCaseOf, ApplyAnnotCaseOfOuter, ApplyAnnotCaseOfInner, MatchAnnotCaseOf

pattern CaseOf   :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> Term Prd -> [TermCase pc] -> Term pc
pattern CaseOf loc rep ty ns t cases <- 
  MuAbs loc MuAnnotCaseOf rep ty Nothing (shiftCmd ShiftDown -> Apply _ ApplyAnnotCaseOfOuter _ t (XCase _ MatchAnnotCaseOf CnsRep _ ns (map (resugarTermCase rep) -> cases)))


-- CocaseOf:
--  [[cocase e of { Dtor(xs) => prd }]] = mu k. < cocase { Dtor(xs) => < [[prd]] | k > }  | [[e]] >
--  [[cocase e of { Dtor(xs) => cns }]] = mu k. < cocase { Dtor(xs) => < k  |  [[cns ]]}  | [[e]] >
--  Annotations used on RHS: MuAnnotCocaseOf, ApplyAnnotCocaseOfOuter, ApplyAnnotCocaseOfInner, MatchAnnotCocaseOf

pattern CocaseOf   :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) ->  NominalStructural -> Term Cns -> [TermCase pc] -> Term pc
pattern CocaseOf loc rep ty ns t cases <- 
  MuAbs loc MuAnnotCocaseOf rep ty Nothing (shiftCmd ShiftDown -> Apply _ ApplyAnnotCocaseOfOuter _ (XCase _ MatchAnnotCocaseOf PrdRep _ ns (map (resugarTermCase rep) -> cases)) t)

resugarCmdCase' :: PrdCnsRep pc -> CmdCase -> TermCaseI pc
resugarCmdCase' PrdRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotXCaseI i) _ t (BoundVar _ CnsRep _ (0,_)))) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase' CnsRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotXCaseI i) _ (BoundVar _ PrdRep _ (0,_)) t)) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase' _ cmd = error $ "cannot resugar " ++ show cmd

-- CaseI:
--   [[case { Ctor(xs,*,ys) => prd }]] = case { Ctor(xs,k,ys) => < [[prd]] | k > }
--   [[case { Ctor(xs,*,ys) => cns }]] = case { Ctor(xs,k,ys) => < k | [[cns]] > }
--   Annotations used on RHS: MatchAnnotCaseI, ApplyAnnotCaseI

pattern CaseI :: Loc -> PrdCnsRep pc -> Typ Neg -> NominalStructural -> [TermCaseI pc] -> Term Cns            
pattern CaseI loc rep ty ns cases <- XCase loc MatchAnnotCaseI (flipPrdCns -> rep) ty ns (map (resugarCmdCase' rep) -> cases)   


-- CocaseI:
--   [[cocase { Dtor(xs,*,ys) => prd }]] = cocase { Dtor(xs,k,ys) => < [[prd]] | k > }
--   [[cocase { Dtor(xs,*,ys) => cns }]] = cocase { Dtor(xs,k,ys) => < k | [[cns]] > }
--   Annotations used on RHS: MatchAnnotCocaseI, ApplyAnnotCocaseI

pattern CocaseI :: Loc -> PrdCnsRep pc -> Typ Pos -> NominalStructural -> [TermCaseI pc] -> Term Prd            
pattern CocaseI loc rep ty ns cases <- XCase loc MatchAnnotCocaseI rep ty ns (map (resugarCmdCase' rep) -> cases)   