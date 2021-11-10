module Translate.Translate
  ( compile
  , compileDecl
  , compileProgram
  , compileSTerm
  , compileCmd
  , compileATerm
  , compileDecl'
  )
  where

import Syntax.STerms
import Syntax.CommonTerm
import Syntax.Program ( Declaration(..), Program )
import Utils ( Twice(..))


resVar :: FreeVarName
resVar = "$result"

compile :: ATerm ext -> STerm Prd Compiled
-- we want to compile e.D(args')
-- Mu k.[(compile e) >> D (compile <$> args')[k] ]
compile (Dtor _ xt t args) =
  let
    cmd = Apply () (compile t) (XtorCall () CnsRep xt $ MkXtorArgs (compile <$> args) [FreeVar () CnsRep resVar])
  in
    MuAbs () PrdRep Nothing $ commandClosingSingle CnsRep resVar $ shiftCmd cmd
-- we want to compile match t { C (args) => e1 }
-- Mu k.[ (compile t) >> match {C (args) => (compile e1) >> k } ]
compile (Match _ t cases)   =
  let
    compileMatchCase (MkACase _ xt args t) = MkSCase xt (Twice (const Nothing <$> args) [])   $ Apply () (compile t) (FreeVar () CnsRep resVar)
    cmd = Apply () (compile t) (XMatch () CnsRep Nominal  (compileMatchCase <$> cases))
  in
    MuAbs () PrdRep Nothing $ commandClosingSingle CnsRep resVar $ shiftCmd cmd
-- we want to compile comatch { D(args) => e }
-- comatch { D(args)[k] => (compile e) >> k }
compile (Comatch _ cocases) =
  let
    compileComatchCase (MkACase _ xt args t) = MkSCase xt (Twice (const Nothing <$> args) [Nothing]) $ Apply () (compile t) (BoundVar () CnsRep (0,0))
  in
    XMatch () PrdRep Nominal $ compileComatchCase <$> cocases


compileSTerm :: STerm pc ext -> STerm pc Compiled
compileSTerm (BoundVar _ pc idx) = BoundVar () pc idx
compileSTerm (FreeVar _ pc fv) = FreeVar () pc fv
compileSTerm (XtorCall _ pc xt MkXtorArgs {prdArgs, cnsArgs}) = XtorCall () pc xt (MkXtorArgs (compileSTerm <$> prdArgs) (compileSTerm <$> cnsArgs))
compileSTerm (MuAbs _ pc bs cmd) = MuAbs () pc bs (compileCmd cmd)
compileSTerm (XMatch _ pc ns cases) = XMatch () pc ns (compileSCase <$> cases)
  where
    compileSCase (MkSCase xt args cmd) = MkSCase xt args (compileCmd cmd)

compileCmd :: Command ext -> Command Compiled
compileCmd (Apply _ prd cns) = Apply () (compileSTerm prd) (compileSTerm cns)
compileCmd (Print _ prd) = Print () (compileSTerm prd)
compileCmd (Done _) = Done ()

compileDecl :: Declaration ext -> Declaration Compiled
compileDecl (PrdCnsDecl _ pc isRec fv annot tm) = PrdCnsDecl () pc isRec fv annot (compileSTerm tm)
compileDecl (CmdDecl _ fv cmd)            = CmdDecl () fv (compileCmd cmd)
compileDecl (DataDecl _ decl)             = DataDecl () decl
compileDecl (ImportDecl _ mn)             = ImportDecl () mn
compileDecl (SetDecl _ txt)               = SetDecl () txt
compileDecl ParseErrorDecl                = ParseErrorDecl   

compileDecl' :: Declaration ext -> Declaration Compiled
compileDecl' (PrdCnsDecl _ pc isRec fv annot tm) = PrdCnsDecl () pc isRec fv annot (compileSTerm tm)
compileDecl' (CmdDecl _ fv cmd)            = CmdDecl () fv (compileCmd cmd)
compileDecl' (DataDecl _ decl)             = DataDecl () decl
compileDecl' (ImportDecl _ mn)             = ImportDecl () mn
compileDecl' (SetDecl _ txt)               = SetDecl () txt
compileDecl' ParseErrorDecl                = ParseErrorDecl   

compileProgram :: Program ext -> Program Compiled
compileProgram ps = compileDecl <$> ps

compileATerm :: ATerm ext -> ATerm Compiled
compileATerm (Dtor _ xt a args) = Dtor () xt (compileATerm a) (compileATerm <$> args)
compileATerm (Match _ a cases) = Match () (compileATerm a) (compileACase <$> cases)
compileATerm (Comatch _ cocases) = Comatch () (compileACase <$> cocases)

compileACase :: ACase ext -> ACase Compiled
compileACase (MkACase _ name args tm) = MkACase () name args (compileATerm tm)