module Translate.Translate 
  (compile)
  where

import Syntax.STerms
import Syntax.ATerms

import Utils


compile :: ATerm ext a -> STerm Prd () ()
compile (BVar _ i) = BoundVar PrdRep i 
compile (FVar _ n) = FreeVar PrdRep n
compile (Ctor _ xt args')   = XtorCall PrdRep xt $ compileArgs args' []
-- we want to compile e.D(args')
-- Mu k.[(compile e) >> D (compile <$> args')[k] ]
compile (Dtor _ xt t args') = shiftAllOnce $ 
                              MuAbs PrdRep () $
                                Apply (compile t) $
                                       XtorCall CnsRep xt $ compileArgs args' [BoundVar CnsRep (0,0)]
-- we want to compile match t { C (args) => e1 }
-- Mu k.[ (compile t) >> match {C (args) => (compile e1) >> k } ]
compile (Match _ t cases)   = MuAbs PrdRep () $ 
                              Apply (shiftAllOnce (compile t)) $ 
                                     XMatch CnsRep Nominal $ shiftCase PrdRep 0 <$> ((aToSCase PrdRep) <$> cases)
-- we want to compile comatch { D(args) => e }
-- comatch { D(args)[k] => (compile e) >> k }
compile (Comatch _ cocases) = XMatch PrdRep Nominal $ (aToSCase CnsRep) <$> cocases


compileArgs :: [ATerm ext a] -> [STerm Cns () ()] -> XtorArgs () ()
compileArgs args' cnsLst = MkXtorArgs (compile <$> args') cnsLst

aToSCase :: PrdCnsRep pc -> ACase ext a -> SCase () ()
-- we want to compile: C (args) => t
-- C (args) => (compile t) >> k 
aToSCase PrdRep (MkACase _ xt args t) = MkSCase xt (Twice (const () <$> args) [])   $ Apply (compile t) (BoundVar CnsRep (1,0))
-- we want to compile: D(args) => t
-- D(args)[k] => (compile t) >> k 
aToSCase _      (MkACase _ xt args t) = MkSCase xt (Twice (const () <$> args) [()]) $ Apply (compile t) (BoundVar CnsRep (0,0))


-- Shift indexes
shiftAllOnce :: STerm Prd () () -> STerm Prd () ()
shiftAllOnce = shift 0


shift :: Int -> STerm Prd () () -> STerm Prd () ()
shift k bv@(BoundVar pc (i,j)) | k <= i    = BoundVar pc (i+1,j)
                                | otherwise = bv
shift _ fv@(FreeVar _ _)   = fv
--Ctor
shift k (XtorCall PrdRep xt (MkXtorArgs prds [])) = XtorCall PrdRep xt (MkXtorArgs (shift k <$> prds) [])
--Dtor
shift k (MuAbs PrdRep () (Apply  t (XtorCall CnsRep xt (MkXtorArgs args' [BoundVar CnsRep (j,0)])))) =
  MuAbs PrdRep () $ Apply  (shift k t) $ XtorCall CnsRep xt $ MkXtorArgs (shift k <$> args') [BoundVar CnsRep (j,0)]
--Match
shift k (MuAbs PrdRep () (Apply t (XMatch CnsRep Nominal cases))) =
  MuAbs PrdRep () $ Apply (shift (k+1) t) $ XMatch CnsRep Nominal $ shiftCase PrdRep (k+1) <$> cases
--Comatch
shift k (XMatch PrdRep Nominal cocases) = XMatch PrdRep Nominal $ shiftCase CnsRep k <$> cocases
shift _ _ = error "Input can't be an STerm produced through translation of ATerms."


shiftCase :: PrdCnsRep pc -> Int -> SCase () () -> SCase () ()
-- shift SCase produced through Match
shiftCase PrdRep k (MkSCase xt (Twice args []) (Apply t (BoundVar CnsRep (j,0)))) =
  MkSCase xt (Twice args []) (Apply (shift (k+1) t) (BoundVar CnsRep (j,0)))
-- shift SCase produced through Comatch
shiftCase _      k (MkSCase xt (Twice args [()]) (Apply t (BoundVar CnsRep (j,0)))) =
  MkSCase xt (Twice args [()]) $ Apply (shift (k+1) t) (BoundVar CnsRep (j,0))
shiftCase _ _ _ = error "Input can't be an SCase produced through translation of ACases."
