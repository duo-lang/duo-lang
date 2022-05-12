module Sugar.Core(
  pattern CaseOfCmd,
  pattern CocaseOfCmd,
  TermCaseI (..),
  PatternI (..),
  pattern CaseOfI,
  pattern CocaseOfI,
  SubstitutionI,
  pattern Semi,
  pattern Dtor,
  TermCase (..),
  pattern CaseOf,
  pattern CocaseOf,
  pattern XCaseI,
  pattern RawCase,
  pattern RawXtor, 
  pattern RawMuAbs,
  pattern RawApply)
  where

import Syntax.Core.Terms
import Syntax.Common
import Utils
import Syntax.AST.Terms (ShiftDirection(..) )
import Syntax.Common.Pattern

-- CaseOfCmd:
--   [[case e of { Ctor(xs) => cmd }]] = < [[e]] | case { Ctor(xs) => [[cmd]] } >
--   Annotations used on RHS: ApplyAnnotCaseOfCmd, MatchAnnotCaseOfCmd

pattern CaseOfCmd :: Loc -> NominalStructural -> Term Prd -> [CmdCase] -> Command
pattern CaseOfCmd loc ns t cases <- Apply loc ApplyAnnotCaseOfCmd t (XCase _ MatchAnnotCaseOfCmd CnsRep ns cases)
 where
    CaseOfCmd loc ns t cases = Apply loc ApplyAnnotCaseOfCmd t (XCase loc MatchAnnotCaseOfCmd CnsRep ns cases)

-- CocaseOfCmd:
--   [[cocase e of { Dtor(xs) => cmd }]] = < cocase { Dtor(xs) => [[cmd]] } | [[e]] >
--   Annotations used on RHS: ApplyAnnotCocaseOfCmd, MatchAnnotCocaseOfCmd

pattern CocaseOfCmd :: Loc -> NominalStructural -> Term Cns -> [CmdCase] -> Command
pattern CocaseOfCmd loc ns t cases <- Apply loc ApplyAnnotCocaseOfCmd (XCase _ MatchAnnotCocaseOfCmd PrdRep ns cases) t
 where
    CocaseOfCmd loc ns t cases = Apply loc ApplyAnnotCocaseOfCmd (XCase loc MatchAnnotCocaseOfCmd PrdRep ns cases) t

mySplitAt :: Int -> [a] -> ([a],(), [a])
mySplitAt n x = (a, (), tail b)
  where (a,b) = splitAt n x


data TermCaseI (pc :: PrdCns) = MkTermCaseI
  { tmcasei_loc  :: Loc
  , tmcasei_pat :: PatternI
  , tmcasei_term :: Term pc
  }
resugarCmdCase :: PrdCnsRep pc -> CmdCase -> TermCaseI pc
resugarCmdCase PrdRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotXCaseOfIInner i) t {-(BoundVar _ CnsRep (0,_))-} _)) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase CnsRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotXCaseOfIInner i) {-(BoundVar _ PrdRep (0,_))-} _ t)) =
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
  Apply loc ApplyAnnotCaseOfIOuter t (XCase _ MatchAnnotCaseOfI (flipPrdCns -> rep) ns (map (resugarCmdCase rep) -> cases))
  where
    CaseOfI loc PrdRep ns t cases =
     let
       desugarmatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotXCaseOfIInner $ length as1) t (BoundVar loc CnsRep (0,length as1))
     in
       Apply loc ApplyAnnotCaseOfIOuter t (XCase loc MatchAnnotCaseOfI CnsRep ns $ desugarmatchCase <$> cases)
    CaseOfI loc CnsRep ns t cases =
     let
       desugarmatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotXCaseOfIInner $ length as1)  (BoundVar loc PrdRep (0,length as1)) t
     in
       Apply loc ApplyAnnotCaseOfIOuter t (XCase loc MatchAnnotCaseOfI CnsRep ns $ desugarmatchCase <$> cases)



-- CocaseOfI:
--   [[cocase e of { Dtor(xs,*,ys) => prd }]] =
--      < cocase { Dtor(xs,k,ys) => < [[prd]] | k > } | [[e]] >
--   [[cocase e of { Dtor(xs,*,ys) => cns }]] =
--      < cocase { Dtor(xs,k,ys) => < k | [[cns]] > } | [[e]] >
--   Annotations used on RHS: ApplyAnnotCaseOfIInner, ApplyAnnotCaseOfIOuter, MatchAnnotCaseOfI

pattern CocaseOfI :: Loc -> PrdCnsRep pc -> NominalStructural -> Term Cns -> [TermCaseI pc] -> Command
pattern CocaseOfI loc rep ns t cases <-
  Apply loc ApplyAnnotCocaseOfIOuter (XCase _ MatchAnnotCocaseOfI (flipPrdCns -> rep) ns (map (resugarCmdCase rep) -> cases)) t
  where
    CocaseOfI loc PrdRep ns t cases =
     let
       desugarcomatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotXCaseOfIInner $ length as1) t (BoundVar loc CnsRep (0,length as1))
     in
       Apply loc ApplyAnnotCocaseOfIOuter (XCase loc MatchAnnotCocaseOfI PrdRep ns $ desugarcomatchCase <$> cases) t
    CocaseOfI loc CnsRep ns t cases =
     let
       desugarcomatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
         let pat = XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2)  in
         MkCmdCase loc pat $ Apply loc (ApplyAnnotXCaseOfIInner $ length as1)  (BoundVar loc PrdRep (0,length as1)) t
     in
       Apply loc ApplyAnnotCocaseOfIOuter (XCase loc MatchAnnotCocaseOfI PrdRep ns $ desugarcomatchCase <$> cases) t

pattern RawApply ::  Loc -> Term Prd -> Term Cns -> Command
pattern RawApply loc t1 t2 = Apply loc ApplyAnnotOrig t1 t2

{-# COMPLETE RawApply, CocaseOfI, CaseOfI, CocaseOfCmd, CaseOfCmd , Print, Read, Jump, ExitSuccess, ExitFailure, PrimOp #-}


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
    MuAbs loc MuAnnotSemi rep _ (shiftCmd ShiftDown -> Apply _ ApplyAnnotSemi (Xtor _ (XtorAnnotSemi i) PrdRep ns xt (resugarSubst rep i -> substi)) t)
    where 
        Semi loc PrdRep ns xt (args1, PrdRep, args2) t = 
            let
                args = args1 ++ [CnsTerm $ FreeVar loc CnsRep resVar] ++ args2
                cmd = Apply loc ApplyAnnotSemi  (Xtor loc (XtorAnnotSemi (length args1)) PrdRep ns xt args) t
            in
            MuAbs loc MuAnnotSemi PrdRep Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd ShiftUp cmd
        Semi loc CnsRep ns xt (args1, CnsRep, args2) t =  
            let
                args = args1 ++ [PrdTerm $ FreeVar loc PrdRep resVar] ++ args2
                cmd = Apply loc ApplyAnnotSemi  (Xtor loc (XtorAnnotSemi (length args1)) PrdRep ns xt args) t
            in
            MuAbs loc MuAnnotSemi CnsRep Nothing $ commandClosing [(Prd, resVar)] $ shiftCmd ShiftUp cmd

-- Dtor:
--   [[e.Dtor(as,*,bs)]]    = mu k. <  [[e]]  | Dtor([[as]], k, [[bs]])
--   Annotations used on RHS: MuAnnotDtor, ApplyAnnotDtor, XtorAnnotDtor

pattern Dtor :: Loc -> PrdCnsRep pc -> NominalStructural -> XtorName -> Term Prd -> SubstitutionI pc -> Term pc
pattern Dtor loc rep ns xt t substi <-
    MuAbs loc MuAnnotDtor rep _ (shiftCmd ShiftDown -> Apply _ ApplyAnnotDtor t (Xtor _ (XtorAnnotDtor i) CnsRep ns xt (resugarSubst rep i -> substi)) )
    where 
        Dtor loc PrdRep ns xt t (args1, PrdRep, args2)  = 
            let
                args = args1 ++ [CnsTerm $ FreeVar loc CnsRep resVar] ++ args2
                cmd = Apply loc ApplyAnnotDtor t (Xtor loc (XtorAnnotDtor (length args1)) CnsRep ns xt args) 
            in
            MuAbs loc MuAnnotDtor PrdRep Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd ShiftUp cmd
        Dtor loc CnsRep ns xt t (args1, CnsRep, args2)  =  
            let
                args = args1 ++ [PrdTerm $ FreeVar loc PrdRep resVar] ++ args2
                cmd = Apply loc ApplyAnnotDtor  t (Xtor loc (XtorAnnotDtor (length args1)) CnsRep ns xt args) 
            in
            MuAbs loc MuAnnotDtor CnsRep Nothing $ commandClosing [(Prd, resVar)] $ shiftCmd ShiftUp cmd

data TermCase (pc :: PrdCns) = MkTermCase
  { tmcase_loc  :: Loc
  , tmcase_pat :: Pattern
  , tmcase_term :: Term pc
  }        

resugarTermCase :: PrdCnsRep pc -> CmdCase -> TermCase pc
resugarTermCase PrdRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ _ t {-(FreeVar _ CnsRep _)-} _ )) =
                     MkTermCase loc (XtorPat loc xt cases) t
resugarTermCase CnsRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ _  {-(FreeVar _ PrdRep _)-} _ t)) =
                     MkTermCase loc (XtorPat loc xt cases) t    
resugarTermCase _ cmd = error $ "compiler bug: resugarTermCase : cannot resugar " ++ show cmd                                  

-- CaseOf:
--  [[case e of { Ctor(xs) => prd }]] = mu k. < [[e]]  |  case { Ctor(xs) => < [[prd]]  |  k > }
--  [[case e of { Ctor(xs) => cns }]] = mu k. < [[e]]  |  case { Ctor(xs) => < k  | [[cns]] > }
--  Annotations used on RHS: MuAnnotCaseOf, ApplyAnnotCaseOfOuter, ApplyAnnotCaseOfInner, MatchAnnotCaseOf

pattern CaseOf   :: Loc -> PrdCnsRep pc ->  NominalStructural -> Term Prd -> [TermCase pc] -> Term pc
pattern CaseOf loc rep ns t cases <- 
  MuAbs loc MuAnnotCaseOf rep Nothing (shiftCmd ShiftDown -> Apply _ ApplyAnnotCaseOfOuter t (XCase _ MatchAnnotCaseOf CnsRep ns (map (resugarTermCase rep) -> cases)))
  where   
    CaseOf loc PrdRep ns t cases =      
        let
            desugarMatchCase (MkTermCase _ pat t) = MkCmdCase loc pat  $ Apply loc ApplyAnnotCaseOfInner t (FreeVar loc CnsRep resVar)
            cmd = Apply loc ApplyAnnotCaseOfOuter t (XCase loc MatchAnnotCaseOf CnsRep ns  (desugarMatchCase <$> cases))
        in
            MuAbs loc MuAnnotCaseOf PrdRep Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd ShiftUp cmd
    CaseOf loc CnsRep ns t cases =        
        let
            desugarMatchCase (MkTermCase _ pat t) = MkCmdCase loc pat  $ Apply loc ApplyAnnotCaseOfInner (FreeVar loc PrdRep  resVar) t
            cmd = Apply loc ApplyAnnotCaseOfOuter t (XCase loc MatchAnnotCaseOf CnsRep ns  (desugarMatchCase <$> cases))
        in
            MuAbs loc MuAnnotCaseOf CnsRep Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd ShiftUp cmd



-- CocaseOf:
--  [[cocase e of { Dtor(xs) => prd }]] = mu k. < cocase { Dtor(xs) => < [[prd]] | k > }  | [[e]] >
--  [[cocase e of { Dtor(xs) => cns }]] = mu k. < cocase { Dtor(xs) => < k  |  [[cns ]]}  | [[e]] >
--  Annotations used on RHS: MuAnnotCocaseOf, ApplyAnnotCocaseOfOuter, ApplyAnnotCocaseOfInner, MatchAnnotCocaseOf

pattern CocaseOf   :: Loc -> PrdCnsRep pc ->  NominalStructural -> Term Cns -> [TermCase pc] -> Term pc
pattern CocaseOf loc rep ns t cases <- 
  MuAbs loc MuAnnotCocaseOf rep Nothing (shiftCmd ShiftDown -> Apply _ ApplyAnnotCocaseOfOuter (XCase _ MatchAnnotCocaseOf PrdRep ns (map (resugarTermCase rep) -> cases)) t)
  where   
    CocaseOf loc PrdRep ns t cases =      
        let
            desugarComatchCase (MkTermCase _ pat t) = MkCmdCase loc pat  $ Apply loc ApplyAnnotCocaseOfInner t (FreeVar loc CnsRep resVar)
            cmd = Apply loc ApplyAnnotCocaseOfOuter (XCase loc MatchAnnotCocaseOf PrdRep ns  (desugarComatchCase <$> cases) ) t  
        in
            MuAbs loc MuAnnotCocaseOf PrdRep Nothing $ commandClosing [(Prd, resVar)] $ shiftCmd ShiftUp cmd
    CocaseOf loc CnsRep ns t cases =        
        let
            desugarComatchCase (MkTermCase _ pat t) = MkCmdCase loc pat  $ Apply loc ApplyAnnotCocaseOfInner (FreeVar loc PrdRep  resVar) t
            cmd = Apply loc ApplyAnnotCocaseOfOuter (XCase loc MatchAnnotCocaseOf PrdRep ns  (desugarComatchCase <$> cases)) t
        in
            MuAbs loc MuAnnotCocaseOf CnsRep Nothing $ commandClosing [(Prd, resVar)] $ shiftCmd ShiftUp cmd

resugarCmdCase' :: PrdCnsRep pc -> CmdCase -> TermCaseI pc
resugarCmdCase' PrdRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotXCaseI i) t {-(BoundVar _ CnsRep (0,_))-} _ )) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase' CnsRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotXCaseI i) {-(BoundVar _ PrdRep (0,_))-} _ t)) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase' _ cmd = error $ "cannot resugar " ++ show cmd

-- XCaseI unifies CaseI and CocaseI
-- CaseI:
--   [[case { Ctor(xs,*,ys) => prd }]] = case { Ctor(xs,k,ys) => < [[prd]] | k > }
--   [[case { Ctor(xs,*,ys) => cns }]] = case { Ctor(xs,k,ys) => < k | [[cns]] > }
-- CocaseI:
--   [[cocase { Dtor(xs,*,ys) => prd }]] = cocase { Dtor(xs,k,ys) => < [[prd]] | k > }
--   [[cocase { Dtor(xs,*,ys) => cns }]] = cocase { Dtor(xs,k,ys) => < k | [[cns]] > }
--   Annotations used on RHS: MatchAnnotXCaseI, ApplyAnnotXCaseI

pattern XCaseI :: Loc -> PrdCnsRep pc -> PrdCnsRep pc' -> NominalStructural -> [TermCaseI pc] -> Term pc'            
pattern XCaseI loc rep rep' ns cases <- XCase loc (MatchAnnotXCaseI rep) rep' ns (map (resugarCmdCase' rep) -> cases)   
  where 
   XCaseI loc PrdRep rep' ns cases =    
    let
        desugarmatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
          let pat = XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2) in
          MkCmdCase loc pat $ Apply loc (ApplyAnnotXCaseI $ length as1) t (BoundVar loc CnsRep (0,length as1))
    in
        XCase loc (MatchAnnotXCaseI PrdRep) rep' ns $ desugarmatchCase <$> cases
   XCaseI loc CnsRep rep' ns cases =    
    let
        desugarmatchCase (MkTermCaseI _ (XtorPatI loc xt (as1, (), as2)) t) =
          let pat = XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2) in
          MkCmdCase loc pat $ Apply loc (ApplyAnnotXCaseI $ length as1) (BoundVar loc PrdRep (0,length as1)) t
    in
        XCase loc (MatchAnnotXCaseI CnsRep) rep' ns $ desugarmatchCase <$> cases

pattern RawCase ::  Loc -> PrdCnsRep pc -> NominalStructural -> [CmdCase] -> Term pc
pattern RawCase loc pc ns cases = XCase loc MatchAnnotOrig pc ns cases 

pattern RawXtor :: Loc -> PrdCnsRep pc -> NominalStructural -> XtorName -> Substitution -> Term pc
pattern RawXtor loc pc ns xt subst = Xtor loc XtorAnnotOrig pc ns xt subst 

pattern RawMuAbs :: Loc -> PrdCnsRep pc -> Maybe FreeVarName -> Command -> Term pc
pattern RawMuAbs loc pc name cmd = MuAbs loc MuAnnotOrig pc name cmd 

{-# COMPLETE RawCase, RawXtor, RawMuAbs, XCaseI, CocaseOf, CaseOf, Dtor, Semi, BoundVar, FreeVar, PrimLitI64, PrimLitF64 #-}
