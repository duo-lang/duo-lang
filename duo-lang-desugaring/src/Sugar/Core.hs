module Sugar.Core(
  pattern CaseOfCmd,
  pattern CocaseOfCmd,
  TermCaseI (..),
  RST.PatternI (..),
  pattern CaseOfI,
  pattern CocaseOfI,
  SubstitutionI(..),
  pattern Semi,
  pattern Dtor,
  TermCase (..),
  pattern CaseOf,
  pattern CocaseOf,
  pattern XCaseI,
  pattern RawCase,
  pattern Lambda,
  pattern RawXtor, 
  pattern RawMuAbs,
  pattern RawApply)
  where

import Loc ( Loc )
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Terms ( Command (Print, Read, Jump, ExitSuccess, ExitFailure, PrimOp)
                         , Term(BoundVar, FreeVar, PrimLitI64, PrimLitF64, PrimLitChar, PrimLitString))
import Syntax.Core.Annot
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.CST.Names
import Syntax.RST.Terms qualified as RST
import Syntax.RST.Types (flipPrdCns)
import qualified Syntax.LocallyNameless as LN

-- CaseOfCmd:
--   [[case e of { Ctor(xs) => cmd }]] = < [[e]] | case { Ctor(xs) => [[cmd]] } >
--   Annotations used on RHS: ApplyAnnotCaseOfCmd, MatchAnnotCaseOfCmd

pattern CaseOfCmd :: Loc -> RST.NominalStructural -> Core.Term Prd -> [Core.CmdCase] -> Core.Command
pattern CaseOfCmd loc ns t cases <- Core.Apply loc ApplyAnnotCaseOfCmd t (Core.XCase _ MatchAnnotCaseOfCmd CnsRep ns cases)
 where
    CaseOfCmd loc ns t cases = Core.Apply loc ApplyAnnotCaseOfCmd t (Core.XCase loc MatchAnnotCaseOfCmd CnsRep ns cases)

-- CocaseOfCmd:
--   [[cocase e of { Dtor(xs) => cmd }]] = < cocase { Dtor(xs) => [[cmd]] } | [[e]] >
--   Annotations used on RHS: ApplyAnnotCocaseOfCmd, MatchAnnotCocaseOfCmd

pattern CocaseOfCmd :: Loc -> RST.NominalStructural -> Core.Term Cns -> [Core.CmdCase] -> Core.Command
pattern CocaseOfCmd loc ns t cases <- Core.Apply loc ApplyAnnotCocaseOfCmd (Core.XCase _ MatchAnnotCocaseOfCmd PrdRep ns cases) t
 where
    CocaseOfCmd loc ns t cases = Core.Apply loc ApplyAnnotCocaseOfCmd (Core.XCase loc MatchAnnotCocaseOfCmd PrdRep ns cases) t

mySplitAt :: Int -> [a] -> ([a],(), [a])
mySplitAt n x = (a, (), tail b)
  where (a,b) = splitAt n x


data TermCaseI (pc :: PrdCns) = MkTermCaseI
  { tmcasei_loc  :: Loc
  , tmcasei_pat :: RST.PatternI
  , tmcasei_term :: Core.Term pc
  }
resugarCmdCase :: PrdCnsRep pc -> Core.CmdCase -> TermCaseI pc
resugarCmdCase PrdRep (Core.MkCmdCase loc (Core.XtorPat _ xt cases)
                (Core.Apply _ (ApplyAnnotXCaseOfIInner i) t {-(BoundVar _ CnsRep (0,_))-} _)) =
                      MkTermCaseI loc (RST.XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase CnsRep (Core.MkCmdCase loc (Core.XtorPat _ xt cases)
                (Core.Apply _ (ApplyAnnotXCaseOfIInner i) {-(BoundVar _ PrdRep (0,_))-} _ t)) =
                      MkTermCaseI loc (RST.XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase _ cmd = error $ "cannot resugar " ++ show cmd


-- CaseOf:
--   [[case e of { Ctor(xs,*,ys) => prd }]] =
--      < [[e]] | case { Ctor(xs,k,ys) => < [[prd]] | k >} >
--   [[case e of { Ctor(xs,*,ys) => cns }]] =
--      < [[e]] | case { Ctor(xs,k,ys) => < k | [[cns]] > } >
--   Annotations used on RHS: ApplyAnnotCaseOfIInner, ApplyAnnotCaseOfIOuter, MatchAnnotCaseOfI

pattern CaseOfI :: Loc -> PrdCnsRep pc -> RST.NominalStructural -> Core.Term Prd -> [TermCaseI pc] -> Core.Command
pattern CaseOfI loc rep ns t cases <-
  Core.Apply loc ApplyAnnotCaseOfIOuter t (Core.XCase _ MatchAnnotCaseOfI (flipPrdCns -> rep) ns (map (resugarCmdCase rep) -> cases))
  where
    CaseOfI loc PrdRep ns t cases =
     let
       desugarmatchCase (MkTermCaseI _ (RST.XtorPatI loc xt (as1, (), as2)) t) =
         let pat = Core.XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2)  in
         Core.MkCmdCase loc pat $ Core.Apply loc (ApplyAnnotXCaseOfIInner $ length as1) t (BoundVar loc CnsRep (0,length as1))
     in
       Core.Apply loc ApplyAnnotCaseOfIOuter t (Core.XCase loc MatchAnnotCaseOfI CnsRep ns $ desugarmatchCase <$> cases)
    CaseOfI loc CnsRep ns t cases =
     let
       desugarmatchCase (MkTermCaseI _ (RST.XtorPatI loc xt (as1, (), as2)) t) =
         let pat = Core.XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2)  in
         Core.MkCmdCase loc pat $ Core.Apply loc (ApplyAnnotXCaseOfIInner $ length as1)  (BoundVar loc PrdRep (0,length as1)) t
     in
       Core.Apply loc ApplyAnnotCaseOfIOuter t (Core.XCase loc MatchAnnotCaseOfI CnsRep ns $ desugarmatchCase <$> cases)



-- CocaseOfI:
--   [[cocase e of { Dtor(xs,*,ys) => prd }]] =
--      < cocase { Dtor(xs,k,ys) => < [[prd]] | k > } | [[e]] >
--   [[cocase e of { Dtor(xs,*,ys) => cns }]] =
--      < cocase { Dtor(xs,k,ys) => < k | [[cns]] > } | [[e]] >
--   Annotations used on RHS: ApplyAnnotCaseOfIInner, ApplyAnnotCaseOfIOuter, MatchAnnotCaseOfI

pattern CocaseOfI :: Loc -> PrdCnsRep pc -> RST.NominalStructural -> Core.Term Cns -> [TermCaseI pc] -> Core.Command
pattern CocaseOfI loc rep ns t cases <-
  Core.Apply loc ApplyAnnotCocaseOfIOuter (Core.XCase _ MatchAnnotCocaseOfI (flipPrdCns -> rep) ns (map (resugarCmdCase rep) -> cases)) t
  where
    CocaseOfI loc PrdRep ns t cases =
     let
       desugarcomatchCase (MkTermCaseI _ (RST.XtorPatI loc xt (as1, (), as2)) t) =
         let pat = Core.XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2)  in
         Core.MkCmdCase loc pat $ Core.Apply loc (ApplyAnnotXCaseOfIInner $ length as1) t (BoundVar loc CnsRep (0,length as1))
     in
       Core.Apply loc ApplyAnnotCocaseOfIOuter (Core.XCase loc MatchAnnotCocaseOfI PrdRep ns $ desugarcomatchCase <$> cases) t
    CocaseOfI loc CnsRep ns t cases =
     let
       desugarcomatchCase (MkTermCaseI _ (RST.XtorPatI loc xt (as1, (), as2)) t) =
         let pat = Core.XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2)  in
         Core.MkCmdCase loc pat $ Core.Apply loc (ApplyAnnotXCaseOfIInner $ length as1)  (BoundVar loc PrdRep (0,length as1)) t
     in
       Core.Apply loc ApplyAnnotCocaseOfIOuter (Core.XCase loc MatchAnnotCocaseOfI PrdRep ns $ desugarcomatchCase <$> cases) t



pattern RawApply ::  Loc -> Core.Term Prd -> Core.Term Cns -> Core.Command
pattern RawApply loc t1 t2 = Core.Apply loc ApplyAnnotOrig t1 t2

{-# COMPLETE RawApply, CocaseOfI, CaseOfI, CocaseOfCmd, CaseOfCmd , Print, Read, Jump, ExitSuccess, ExitFailure, PrimOp #-}


newtype SubstitutionI (pc :: PrdCns) = MkSubstitutionI { unSubstitutionI :: ([Core.PrdCnsTerm], PrdCnsRep pc, [Core.PrdCnsTerm]) }

resugarSubst ::  PrdCnsRep pc -> Int -> Core.Substitution -> SubstitutionI pc
resugarSubst rep n x = MkSubstitutionI (a, rep, tail b)
  where (a,b) = splitAt n x.unSubstitution

resVar :: FreeVarName
resVar = MkFreeVarName "$result"

-- Semi:
--   [[Ctor(as,*,bs) ;; e]] = mu k. <  Ctor([[as]],k,[[bs]])  |  [[e]]  >
--   Annotations used on RHS: MuAnnotSemi, ApplyAnnotSemi, XtorAnnotSemi

pattern Semi :: Loc -> PrdCnsRep pc -> RST.NominalStructural -> XtorName -> SubstitutionI pc -> Core.Term Cns -> Core.Term pc
pattern Semi loc rep ns xt substi t <-
    Core.MuAbs loc MuAnnotSemi rep _ (LN.shift LN.ShiftDown -> Core.Apply _ ApplyAnnotSemi (Core.Xtor _ (XtorAnnotSemi i) PrdRep ns xt (resugarSubst rep i -> substi)) t)
    where 
        Semi loc PrdRep ns xt (MkSubstitutionI (args1, PrdRep, args2)) t = 
            let
                args = args1 ++ [Core.CnsTerm $ FreeVar loc CnsRep resVar] ++ args2
                cmd = Core.Apply loc ApplyAnnotSemi  (Core.Xtor loc (XtorAnnotSemi (length args1)) PrdRep ns xt (Core.MkSubstitution args)) t
            in
            Core.MuAbs loc MuAnnotSemi PrdRep Nothing $ LN.close [(Cns, resVar)] $ LN.shift LN.ShiftUp cmd
        Semi loc CnsRep ns xt (MkSubstitutionI (args1, CnsRep, args2)) t =  
            let
                args = args1 ++ [Core.PrdTerm $ FreeVar loc PrdRep resVar] ++ args2
                cmd = Core.Apply loc ApplyAnnotSemi  (Core.Xtor loc (XtorAnnotSemi (length args1)) PrdRep ns xt (Core.MkSubstitution args)) t
            in
            Core.MuAbs loc MuAnnotSemi CnsRep Nothing $ LN.close [(Prd, resVar)] $ LN.shift LN.ShiftUp cmd

-- Dtor:
--   [[e.Dtor(as,*,bs)]]    = mu k. <  [[e]]  | Dtor([[as]], k, [[bs]])
--   Annotations used on RHS: MuAnnotDtor, ApplyAnnotDtor, XtorAnnotDtor

pattern Dtor :: Loc -> PrdCnsRep pc -> RST.NominalStructural -> XtorName -> Core.Term Prd -> SubstitutionI pc -> Core.Term pc
pattern Dtor loc rep ns xt t substi <-
    Core.MuAbs loc MuAnnotDtor rep _ (LN.shift LN.ShiftDown -> Core.Apply _ ApplyAnnotDtor t (Core.Xtor _ (XtorAnnotDtor i) CnsRep ns xt (resugarSubst rep i -> substi)) )
    where 
        Dtor loc PrdRep ns xt t (MkSubstitutionI (args1, PrdRep, args2))  = 
            let
                args = args1 ++ [Core.CnsTerm $ FreeVar loc CnsRep resVar] ++ args2
                cmd = Core.Apply loc ApplyAnnotDtor t (Core.Xtor loc (XtorAnnotDtor (length args1)) CnsRep ns xt (Core.MkSubstitution args))
            in
            Core.MuAbs loc MuAnnotDtor PrdRep Nothing $ LN.close [(Cns, resVar)] $ LN.shift LN.ShiftUp cmd
        Dtor loc CnsRep ns xt t (MkSubstitutionI (args1, CnsRep, args2))  =  
            let
                args = args1 ++ [Core.PrdTerm $ FreeVar loc PrdRep resVar] ++ args2
                cmd = Core.Apply loc ApplyAnnotDtor  t (Core.Xtor loc (XtorAnnotDtor (length args1)) CnsRep ns xt (Core.MkSubstitution args))
            in
            Core.MuAbs loc MuAnnotDtor CnsRep Nothing $ LN.close [(Prd, resVar)] $ LN.shift LN.ShiftUp cmd

data TermCase (pc :: PrdCns) = MkTermCase
  { tmcase_loc  :: Loc
  , tmcase_pat :: Core.Pattern
  , tmcase_term :: Core.Term pc
  }        

resugarTermCase :: PrdCnsRep pc -> Core.CmdCase -> TermCase pc
resugarTermCase PrdRep (Core.MkCmdCase loc (Core.XtorPat _ xt cases)
                (Core.Apply _ _ t {-(FreeVar _ CnsRep _)-} _ )) =
                     MkTermCase loc (Core.XtorPat loc xt cases) t
resugarTermCase CnsRep (Core.MkCmdCase loc (Core.XtorPat _ xt cases)
                (Core.Apply _ _  {-(FreeVar _ PrdRep _)-} _ t)) =
                     MkTermCase loc (Core.XtorPat loc xt cases) t    
resugarTermCase _ cmd = error $ "compiler bug: resugarTermCase : cannot resugar " ++ show cmd                                  

-- CaseOf:
--  [[case e of { Ctor(xs) => prd }]] = mu k. < [[e]]  |  case { Ctor(xs) => < [[prd]]  |  k > }
--  [[case e of { Ctor(xs) => cns }]] = mu k. < [[e]]  |  case { Ctor(xs) => < k  | [[cns]] > }
--  Annotations used on RHS: MuAnnotCaseOf, ApplyAnnotCaseOfOuter, ApplyAnnotCaseOfInner, MatchAnnotCaseOf

pattern CaseOf   :: Loc -> PrdCnsRep pc ->  RST.NominalStructural -> Core.Term Prd -> [TermCase pc] -> Core.Term pc
pattern CaseOf loc rep ns t cases <- 
  Core.MuAbs loc MuAnnotCaseOf rep Nothing (LN.shift LN.ShiftDown -> Core.Apply _ ApplyAnnotCaseOfOuter t (Core.XCase _ MatchAnnotCaseOf CnsRep ns (map (resugarTermCase rep) -> cases)))
  where   
    CaseOf loc PrdRep ns t cases =      
        let
            desugarMatchCase (MkTermCase _ pat t) = Core.MkCmdCase loc pat  $ Core.Apply loc ApplyAnnotCaseOfInner t (FreeVar loc CnsRep resVar)
            cmd = Core.Apply loc ApplyAnnotCaseOfOuter t (Core.XCase loc MatchAnnotCaseOf CnsRep ns  (desugarMatchCase <$> cases))
        in
            Core.MuAbs loc MuAnnotCaseOf PrdRep Nothing $ LN.close [(Cns, resVar)] $ LN.shift LN.ShiftUp cmd
    CaseOf loc CnsRep ns t cases =        
        let
            desugarMatchCase (MkTermCase _ pat t) = Core.MkCmdCase loc pat  $ Core.Apply loc ApplyAnnotCaseOfInner (FreeVar loc PrdRep  resVar) t
            cmd = Core.Apply loc ApplyAnnotCaseOfOuter t (Core.XCase loc MatchAnnotCaseOf CnsRep ns  (desugarMatchCase <$> cases))
        in
            Core.MuAbs loc MuAnnotCaseOf CnsRep Nothing $ LN.close [(Cns, resVar)] $ LN.shift LN.ShiftUp cmd



-- CocaseOf:
--  [[cocase e of { Dtor(xs) => prd }]] = mu k. < cocase { Dtor(xs) => < [[prd]] | k > }  | [[e]] >
--  [[cocase e of { Dtor(xs) => cns }]] = mu k. < cocase { Dtor(xs) => < k  |  [[cns ]]}  | [[e]] >
--  Annotations used on RHS: MuAnnotCocaseOf, ApplyAnnotCocaseOfOuter, ApplyAnnotCocaseOfInner, MatchAnnotCocaseOf

pattern CocaseOf   :: Loc -> PrdCnsRep pc ->  RST.NominalStructural -> Core.Term Cns -> [TermCase pc] -> Core.Term pc
pattern CocaseOf loc rep ns t cases <- 
  Core.MuAbs loc MuAnnotCocaseOf rep Nothing (LN.shift LN.ShiftDown -> Core.Apply _ ApplyAnnotCocaseOfOuter (Core.XCase _ MatchAnnotCocaseOf PrdRep ns (map (resugarTermCase rep) -> cases)) t)
  where   
    CocaseOf loc PrdRep ns t cases =      
        let
            desugarComatchCase (MkTermCase _ pat t) = Core.MkCmdCase loc pat  $ Core.Apply loc ApplyAnnotCocaseOfInner t (FreeVar loc CnsRep resVar)
            cmd = Core.Apply loc ApplyAnnotCocaseOfOuter (Core.XCase loc MatchAnnotCocaseOf PrdRep ns  (desugarComatchCase <$> cases) ) t  
        in
            Core.MuAbs loc MuAnnotCocaseOf PrdRep Nothing $ LN.close [(Prd, resVar)] $ LN.shift LN.ShiftUp cmd
    CocaseOf loc CnsRep ns t cases =        
        let
            desugarComatchCase (MkTermCase _ pat t) = Core.MkCmdCase loc pat  $ Core.Apply loc ApplyAnnotCocaseOfInner (FreeVar loc PrdRep  resVar) t
            cmd = Core.Apply loc ApplyAnnotCocaseOfOuter (Core.XCase loc MatchAnnotCocaseOf PrdRep ns  (desugarComatchCase <$> cases)) t
        in
            Core.MuAbs loc MuAnnotCocaseOf CnsRep Nothing $ LN.close [(Prd, resVar)] $ LN.shift LN.ShiftUp cmd

resugarCmdCase' :: PrdCnsRep pc -> Core.CmdCase -> TermCaseI pc
resugarCmdCase' PrdRep (Core.MkCmdCase loc (Core.XtorPat _ xt cases)
                (Core.Apply _ (ApplyAnnotXCaseI i) t {-(BoundVar _ CnsRep (0,_))-} _ )) =
                      MkTermCaseI loc (RST.XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase' CnsRep (Core.MkCmdCase loc (Core.XtorPat _ xt cases)
                (Core.Apply _ (ApplyAnnotXCaseI i) {-(BoundVar _ PrdRep (0,_))-} _ t)) =
                      MkTermCaseI loc (RST.XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase' _ cmd = error $ "cannot resugar " ++ show cmd

-- XCaseI unifies CaseI and CocaseI
-- CaseI:
--   [[case { Ctor(xs,*,ys) => prd }]] = case { Ctor(xs,k,ys) => < [[prd]] | k > }
--   [[case { Ctor(xs,*,ys) => cns }]] = case { Ctor(xs,k,ys) => < k | [[cns]] > }
-- CocaseI:
--   [[cocase { Dtor(xs,*,ys) => prd }]] = cocase { Dtor(xs,k,ys) => < [[prd]] | k > }
--   [[cocase { Dtor(xs,*,ys) => cns }]] = cocase { Dtor(xs,k,ys) => < k | [[cns]] > }
--   Annotations used on RHS: MatchAnnotXCaseI, ApplyAnnotXCaseI

pattern XCaseI :: Loc -> PrdCnsRep pc -> PrdCnsRep pc' -> RST.NominalStructural -> [TermCaseI pc] -> Core.Term pc'            
pattern XCaseI loc rep rep' ns cases <- Core.XCase loc (MatchAnnotXCaseI rep) rep' ns (map (resugarCmdCase' rep) -> cases)   
  where 
   XCaseI loc PrdRep rep' ns cases =    
    let
        desugarmatchCase (MkTermCaseI _ (RST.XtorPatI loc xt (as1, (), as2)) t) =
          let pat = Core.XtorPat loc xt (as1 ++ [(Cns,Nothing)] ++ as2) in
          Core.MkCmdCase loc pat $ Core.Apply loc (ApplyAnnotXCaseI $ length as1) t (BoundVar loc CnsRep (0,length as1))
    in
        Core.XCase loc (MatchAnnotXCaseI PrdRep) rep' ns $ desugarmatchCase <$> cases
   XCaseI loc CnsRep rep' ns cases =    
    let
        desugarmatchCase (MkTermCaseI _ (RST.XtorPatI loc xt (as1, (), as2)) t) =
          let pat = Core.XtorPat loc xt (as1 ++ [(Prd,Nothing)] ++ as2) in
          Core.MkCmdCase loc pat $ Core.Apply loc (ApplyAnnotXCaseI $ length as1) (BoundVar loc PrdRep (0,length as1)) t
    in
        Core.XCase loc (MatchAnnotXCaseI CnsRep) rep' ns $ desugarmatchCase <$> cases


-- Lambda:
--   [[\x -> t }]] = cocase { Ap(x,k) => [[t]] >> k}  


extractCmdCase :: PrdCnsRep pc -> [Core.CmdCase] -> Maybe (FreeVarName,Core.Term pc) 
extractCmdCase PrdRep [Core.MkCmdCase _ (Core.XtorPat _ (MkXtorName "Ap") [(Prd,Just fv),(Cns,Nothing)]) (Core.Apply _ ApplyAnnotLambda tm (Core.BoundVar _ CnsRep (0,1)))] = Just (fv,tm)
extractCmdCase CnsRep [Core.MkCmdCase _ (Core.XtorPat _ (MkXtorName "CoAp") [(Cns,Just fv),(Prd,Nothing)]) (Core.Apply _ ApplyAnnotLambda  (Core.BoundVar _ PrdRep (0,1)) tm)] = Just (fv,tm)
extractCmdCase _ _ = Nothing 

pattern Lambda  :: Loc ->  PrdCnsRep pc -> FreeVarName -> Core.Term pc  -> Core.Term pc 
pattern Lambda loc pc fv tm <- Core.XCase loc MatchAnnotLambda pc (RST.Nominal _) (extractCmdCase pc -> Just (fv,tm))
  where 
    Lambda loc PrdRep x tm = Core.XCase loc MatchAnnotLambda PrdRep (RST.Nominal (MkTypeName "Fun")) [Core.MkCmdCase loc (Core.XtorPat loc (MkXtorName "Ap") [(Prd,Just x),(Cns,Nothing)]) (Core.Apply loc ApplyAnnotLambda tm (BoundVar loc CnsRep (0,1)))]  
    Lambda loc CnsRep x tm = Core.XCase loc MatchAnnotLambda CnsRep (RST.Nominal (MkTypeName "CoFun")) [Core.MkCmdCase loc (Core.XtorPat loc (MkXtorName "CoAp") [(Cns,Just x),(Prd,Nothing)]) (Core.Apply loc ApplyAnnotLambda (BoundVar loc PrdRep (0,1)) tm )]  

pattern RawCase ::  Loc -> PrdCnsRep pc -> RST.NominalStructural -> [Core.CmdCase] -> Core.Term pc
pattern RawCase loc pc ns cases = Core.XCase loc MatchAnnotOrig pc ns cases 

pattern RawXtor :: Loc -> PrdCnsRep pc -> RST.NominalStructural -> XtorName -> Core.Substitution -> Core.Term pc
pattern RawXtor loc pc ns xt subst = Core.Xtor loc XtorAnnotOrig pc ns xt subst 

pattern RawMuAbs :: Loc -> PrdCnsRep pc -> Maybe FreeVarName -> Core.Command -> Core.Term pc
pattern RawMuAbs loc pc name cmd = Core.MuAbs loc MuAnnotOrig pc name cmd 

{-# COMPLETE RawCase, RawXtor, RawMuAbs, XCaseI, CocaseOf, Lambda, CaseOf, Dtor, Semi, BoundVar, FreeVar, PrimLitI64, PrimLitF64, PrimLitChar, PrimLitString #-}
