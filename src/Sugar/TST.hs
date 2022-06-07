module Sugar.TST (
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
  pattern RawApply,
  pattern RawCase, 
  pattern RawXtor, 
  pattern RawMuAbs,
  pattern Lambda, 
  isDesugaredTerm,
  isDesugaredCommand,
  resetAnnotationTerm,
  resetAnnotationCmd)
  where

import Syntax.TST.Terms
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
                (Apply _ (ApplyAnnotXCaseOfIInner i) _ t {-(BoundVar _ CnsRep _ (0,_) ) -} _)) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase CnsRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotXCaseOfIInner i) _ {-(BoundVar _ PrdRep _ (0,_))-} _ t)) =
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

pattern RawApply ::  Loc -> Maybe MonoKind -> Term Prd -> Term Cns -> Command
pattern RawApply loc kind t1 t2 = Apply loc ApplyAnnotOrig kind t1 t2

{-# COMPLETE RawApply, CocaseOfI, CaseOfI, CocaseOfCmd, CaseOfCmd, Print, Read, Jump, ExitSuccess, ExitFailure, PrimOp  #-}

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
    MuAbs loc MuAnnotSemi rep ty _ (shiftCmd ShiftDown -> Apply _ ApplyAnnotSemi _ (Xtor _ (XtorAnnotSemi i) PrdRep _ ns xt (resugarSubst rep i -> substi)) t)

-- Dtor:
--   [[e.Dtor(as,*,bs)]]    = mu k. <  [[e]]  | Dtor([[as]], k, [[bs]])
--   Annotations used on RHS: MuAnnotDtor, ApplyAnnotDtor, XtorAnnotDtor

pattern Dtor :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> XtorName -> Term Prd -> SubstitutionI pc -> Term pc
pattern Dtor loc rep ty ns xt t substi <-
    MuAbs loc MuAnnotDtor rep ty _ (shiftCmd ShiftDown -> Apply _ ApplyAnnotDtor _ t (Xtor _ (XtorAnnotDtor i) CnsRep _ ns xt (resugarSubst rep i -> substi)) )

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
                (Apply _ _ _ t {-(FreeVar _ CnsRep _ _)-} _ )) =
                     MkTermCase loc (XtorPat loc xt cases) t
resugarTermCase CnsRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ _ _ {-(FreeVar _ PrdRep _ _ )-} _ t)) =
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
                (Apply _ (ApplyAnnotXCaseI i) _ t {-(BoundVar _ CnsRep _ (0,_))-} _)) =
                      MkTermCaseI loc (XtorPatI loc xt (mySplitAt i cases)) t
resugarCmdCase' CnsRep (MkCmdCase loc (XtorPat _ xt cases)
                (Apply _ (ApplyAnnotXCaseI i) _ {-(BoundVar _ PrdRep _ (0,_))-} _ t)) =
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
 
pattern XCaseI :: Loc -> PrdCnsRep pc -> PrdCnsRep pc' -> Typ (PrdCnsToPol pc') -> NominalStructural -> [TermCaseI pc] -> Term pc'            
pattern XCaseI loc rep rep' ty ns cases <- XCase loc (MatchAnnotXCaseI rep) rep' ty ns (map (resugarCmdCase' rep) -> cases)   

extractCmdCase :: PrdCnsRep pc -> [CmdCase] -> Maybe (FreeVarName,Term pc) 
extractCmdCase PrdRep [MkCmdCase _ (XtorPat _ (MkXtorName "Ap") [(Prd,Just fv),(Cns,Nothing)]) (Apply _ ApplyAnnotLambda _ tm (BoundVar _ CnsRep _ (0,1)))] = Just (fv,tm)
extractCmdCase CnsRep [MkCmdCase _ (XtorPat _ (MkXtorName "CoAp") [(Cns,Just fv),(Prd,Nothing)]) (Apply _ ApplyAnnotLambda _ (BoundVar _ PrdRep _ (0,1)) tm)] = Just (fv,tm)
extractCmdCase _ _ = Nothing 

pattern Lambda  :: Loc ->  PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> FreeVarName -> Term pc  -> Term pc 
pattern Lambda loc pc ty fv tm <- XCase loc MatchAnnotLambda pc ty Nominal (extractCmdCase pc -> Just (fv,tm))

pattern RawCase ::  Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> [CmdCase] -> Term pc
pattern RawCase loc pc ty ns cases = XCase loc MatchAnnotOrig pc ty ns cases 

pattern RawXtor :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> XtorName -> Substitution -> Term pc
pattern RawXtor loc pc ty ns xt subst = Xtor loc XtorAnnotOrig pc ty ns xt subst 

pattern RawMuAbs :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> Maybe FreeVarName -> Command -> Term pc
pattern RawMuAbs loc pc ty name cmd = MuAbs loc MuAnnotOrig pc ty name cmd 

{-# COMPLETE RawCase, RawXtor, RawMuAbs, XCaseI, CocaseOf, CaseOf, Dtor, Semi, Lambda, BoundVar, FreeVar, PrimLitI64, PrimLitF64 #-}

isDesugaredTerm :: Term pc -> Bool 
isDesugaredTerm XCaseI {} = False 
isDesugaredTerm CocaseOf {} = False 
isDesugaredTerm CaseOf {} = False 
isDesugaredTerm Dtor {} = False 
isDesugaredTerm Semi {} = False 
isDesugaredTerm (RawCase _ _ _ _ cases) = 
  and $ (\MkCmdCase { cmdcase_cmd } -> isDesugaredCommand cmdcase_cmd ) <$> cases 
isDesugaredTerm (RawXtor _ _ _ _ _ subst) = 
  and $ isDesugaredPCTerm <$> subst
isDesugaredTerm (RawMuAbs _ _ _ _ cmd) = isDesugaredCommand cmd 
isDesugaredTerm _ = True 

isDesugaredCommand :: Command -> Bool 
isDesugaredCommand CocaseOfI {} = False  
isDesugaredCommand CaseOfI {} = False  
isDesugaredCommand CocaseOfCmd {} = False  
isDesugaredCommand CaseOfCmd {} = False  
isDesugaredCommand (PrimOp _ _ _ subst) =
  and (isDesugaredPCTerm <$> subst)
isDesugaredCommand (RawApply _ _ prd cns) =
  isDesugaredTerm prd && isDesugaredTerm cns
isDesugaredCommand (Print _ prd cmd) =
  isDesugaredTerm prd && isDesugaredCommand cmd
isDesugaredCommand (Read _ cns) =
  isDesugaredTerm cns  
isDesugaredCommand _ = True 

isDesugaredPCTerm :: PrdCnsTerm -> Bool
isDesugaredPCTerm (PrdTerm tm) = isDesugaredTerm tm
isDesugaredPCTerm (CnsTerm tm) = isDesugaredTerm tm

resetAnnotationPC :: PrdCnsTerm -> PrdCnsTerm 
resetAnnotationPC (PrdTerm t) = PrdTerm (resetAnnotationTerm t)
resetAnnotationPC (CnsTerm t) = CnsTerm (resetAnnotationTerm t)

resetAnnotationTerm :: Term pc -> Term pc 
resetAnnotationTerm (Xtor loc _ rep ns ty xt subst) = Xtor loc XtorAnnotOrig rep ns ty xt (resetAnnotationPC <$> subst)
resetAnnotationTerm (MuAbs loc _ rep ty fn cmd) = MuAbs loc MuAnnotOrig rep ty fn (resetAnnotationCmd cmd)
resetAnnotationTerm (XCase loc _ pc ty ns cases) = XCase loc MatchAnnotOrig pc ty ns ((\(MkCmdCase a b cmd) -> (MkCmdCase a b (resetAnnotationCmd cmd)) ) <$> cases )
resetAnnotationTerm t = t 

resetAnnotationCmd :: Command -> Command 
resetAnnotationCmd (PrimOp a b c subst) =
  PrimOp a b c (resetAnnotationPC <$> subst)
resetAnnotationCmd (Apply l _ kind t1 t2) = Apply l ApplyAnnotOrig kind (resetAnnotationTerm t1) (resetAnnotationTerm t2)  
resetAnnotationCmd (Print loc t cmd) = Print loc (resetAnnotationTerm t) (resetAnnotationCmd cmd)
resetAnnotationCmd (Read loc t) = Read loc (resetAnnotationTerm t)
resetAnnotationCmd cmd = cmd   
