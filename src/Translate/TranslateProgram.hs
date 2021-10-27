module Translate.TranslateProgram 
  (compileProgram)
  where

import Translate.Translate (compile)
import Syntax.Program

compileProgram :: Program ext -> Program ()
compileProgram ps = compileDecl <$> ps
  where
    compileDecl :: Declaration ext -> Declaration ()
    compileDecl (DefDecl isRec _ v ts t) = PrdDecl isRec () v ts $ compile t
    compileDecl decl = const () <$> decl
