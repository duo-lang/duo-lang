module Translate.Translate 
  (compile)
  where

import Syntax.STerms
import Syntax.ATerms
--import Data.List (elemIndex)

import Utils
-- import Data.Maybe (isJust)


compile :: ATerm () -> STerm Prd ()
compile (BVar i) = BoundVar PrdRep i 
compile (FVar n) = FreeVar PrdRep n ()
compile (Ctor xt args')   = XtorCall PrdRep xt $ compileArgs args' []
-- we want to compile e.D(args')
-- Mu k.[(compile e) >> D (compile <$> args')[k] ]
compile (Dtor xt t args') = MuAbs PrdRep () $
                                Apply  (compile t) $
                                       XtorCall CnsRep xt $ compileArgs args' [BoundVar CnsRep (0,0)]
-- we want to compile match t { C (args) => e1 }
-- Mu k.[ (compile t) >> match {C (args) => (compile e1) >> k } ]
compile (Match t cases)   = MuAbs PrdRep () $ Apply (shift (compile t)) $ XMatch CnsRep Nominal $ (aToSCase PrdRep) <$> cases
-- we want to compile comatch { D(args) => e }
-- comatch { D(args)[k] => (compile e) >> k }
compile (Comatch cocases) = XMatch PrdRep Nominal $  (aToSCase CnsRep) <$> cocases


compileArgs :: [ATerm ()] -> [STerm Cns ()] -> XtorArgs ()
compileArgs args' cnsLst = MkXtorArgs (compile <$> args') cnsLst

aToSCase :: PrdCnsRep pc -> ACase () -> SCase ()
aToSCase PrdRep (MkACase xt args t) = MkSCase xt (Twice args [])   $ Apply (compile t) (BoundVar CnsRep (0,0))
aToSCase _      (MkACase xt args t) = MkSCase xt (Twice args [()]) $ Apply (compile t) (BoundVar CnsRep (0,0))

shift :: STerm pc () -> STerm pc ()
shift (BoundVar pc (i,j)) = BoundVar pc (i+1,j)
shift (FreeVar pc n ())   = FreeVar pc n ()
shift (XtorCall pc xt (MkXtorArgs prds cns)) = XtorCall pc xt $ MkXtorArgs (shift <$> prds) (shift <$> cns) 
shift (XMatch pc ns sCases) = XMatch pc ns $ shiftCase <$> sCases
shift (MuAbs pc a cmd) = MuAbs pc a $ cmdShift cmd

shiftCase :: SCase () -> SCase ()
shiftCase (MkSCase xt twc cmd) = MkSCase xt twc $ cmdShift cmd

cmdShift :: Command () -> Command ()
cmdShift Done          = Done
cmdShift (Print t)     = Print $ shift t
cmdShift (Apply t1 t2) = Apply (shift t1) (shift t2)

