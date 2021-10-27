module Translate.Translate 
  ( compile
  , compileDecl
  , compileProgram
  )
  where

import Data.Bifunctor ( bimap )
import Syntax.STerms
import Syntax.ATerms ( ACase(..), ATerm(..) )
import Syntax.Program ( Declaration(..), Program )
import Utils ( Twice(..) )


resVar :: FreeVarName 
resVar = "$result"

compile :: ATerm ext a -> STerm Prd () ()
compile (BVar _ i) = BoundVar () PrdRep i
compile (FVar _ n) = FreeVar () PrdRep n
compile (Ctor _ xt args)   = XtorCall () PrdRep xt $ MkXtorArgs (compile <$> args) []
-- we want to compile e.D(args')
-- Mu k.[(compile e) >> D (compile <$> args')[k] ]
compile (Dtor _ xt t args) = 
  let
    cmd = Apply () (compile t) (XtorCall () CnsRep xt $ MkXtorArgs (compile <$> args) [FreeVar () CnsRep resVar])
  in 
    MuAbs () PrdRep () $ commandClosingSingle CnsRep resVar $ shiftCmd cmd
-- we want to compile match t { C (args) => e1 }
-- Mu k.[ (compile t) >> match {C (args) => (compile e1) >> k } ]
compile (Match _ t cases)   =
  let
    compileMatchCase (MkACase _ xt args t) = MkSCase xt (Twice (const () <$> args) [])   $ Apply () (compile t) (FreeVar () CnsRep resVar)
    cmd = Apply () (compile t) (XMatch () CnsRep Nominal  (compileMatchCase <$> cases))
  in
    MuAbs () PrdRep () $ commandClosingSingle CnsRep resVar $ shiftCmd cmd
-- we want to compile comatch { D(args) => e }
-- comatch { D(args)[k] => (compile e) >> k }
compile (Comatch _ cocases) =
  let
    compileComatchCase (MkACase _ xt args t) = MkSCase xt (Twice (const () <$> args) [()]) $ Apply () (compile t) (BoundVar () CnsRep (0,0))
  in
    XMatch () PrdRep Nominal $ compileComatchCase <$> cocases

compileDecl :: Declaration a b -> Declaration () ()
compileDecl (DefDecl isRec _ v ts t) = PrdDecl isRec () v ts $ compile t
compileDecl decl = bimap (const ()) (const ()) decl

compileProgram :: Program a b -> Program () ()
compileProgram ps = compileDecl <$> ps

