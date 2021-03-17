module Translate.Translate 
  (compile)
  where

import Syntax.STerms
import Syntax.ATerms



compile :: ATerm a -> Either (STerm Prd a) (STerm Cns a)
{-
compile (BVar i) = ...
compile (FVar n) = ...
-}
compile (Ctor xt args')   = Left $ XtorCall PrdRep xt $ compileArgs args'
{-
compile (Dtor xt t args') = XtorCall CnsRep xt (...t...) seperatePrdCns $ compile <$> args'
compile (Match t cases)   = XMatch CnsRep  ...NS... (compile t) ...
compile (Comatch cocases) = XMatch PrdRep ... 
-}

compileArgs :: [ATerm a] -> XtorArgs a
compileArgs = compileArgsAcc (MkXtorArgs [] [])
  where
    compileArgsAcc xtorArgs [] = xtorArgs
    compileArgsAcc (MkXtorArgs prds cnss) (tm:rst) =
      case compile tm of
        Left  stm -> compileArgsAcc (MkXtorArgs (stm : prds) cnss) rst
        Right stm -> compileArgsAcc (MkXtorArgs prds (stm : cnss)) rst