module Translate.Translate 
  (compile)
  where

import Syntax.STerms
import Syntax.ATerms



compile :: ATerm a -> STerm Prd a

compile (BVar i) = error "not implemented yet"
compile (FVar n) = error "not implemented yet"
compile (Ctor xt args')   = XtorCall PrdRep xt $ compileArgs args'
compile (Dtor xt t args') = error "not implemented yet"
compile (Match t cases)   = error "not implemented yet"
compile (Comatch cocases) = error "not implemented yet"


compileArgs :: [ATerm a] -> XtorArgs a
compileArgs args = MkXtorArgs (compile <$> args) []