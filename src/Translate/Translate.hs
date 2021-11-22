module Translate.Translate
  ( compile
  , compileProgram
  , compileCmd
  )
  where

import Syntax.Terms
import Syntax.CommonTerm
import Syntax.Program ( Declaration(..), Program )
import Utils ( Twice(..))

---------------------------------------------------------------------------------
-- Translate Terms
---------------------------------------------------------------------------------

resVar :: FreeVarName
resVar = "$result"

compileSubstitution :: Substitution ext -> Substitution Compiled
compileSubstitution (MkSubst prdArgs cnsArgs) = MkSubst (compile <$> prdArgs) (compile <$> cnsArgs)

compile :: Term pc ext -> Term pc Compiled
compile (BoundVar _ pc idx) = BoundVar () pc idx
compile (FreeVar _ pc fv) = FreeVar () pc fv
compile (XtorCall _ pc xt args) = XtorCall () pc xt (compileSubstitution args)
compile (MuAbs _ pc bs cmd) = MuAbs () pc bs (compileCmd cmd)
compile (XMatch _ pc ns cases) = XMatch () pc ns (compileSCase <$> cases)
-- we want to compile e.D(args')
-- Mu k.[(compile e) >> D (compile <$> args')[k] ]
compile (Dtor _ xt t args) =
  let
    cmd = Apply () (compile t) (XtorCall () CnsRep xt $ MkSubst (compile <$> args) [FreeVar () CnsRep resVar])
  in
    MuAbs () PrdRep Nothing $ commandClosingSingle CnsRep resVar $ shiftCmd cmd
-- we want to compile match t { C (args) => e1 }
-- Mu k.[ (compile t) >> match {C (args) => (compile e1) >> k } ]
compile (Match _ t cases)   =
  let
    nominalStructural = case cases of
      [] -> Structural
      ((MkACase _ (MkXtorName ns _ ) _ _):_) -> ns
    compileMatchCase (MkACase _ xt args t) = MkSCase () xt (Twice (const Nothing <$> args) [])   $ Apply () (compile t) (FreeVar () CnsRep resVar)
    cmd = Apply () (compile t) (XMatch () CnsRep nominalStructural  (compileMatchCase <$> cases))
  in
    MuAbs () PrdRep Nothing $ commandClosingSingle CnsRep resVar $ shiftCmd cmd
-- we want to compile comatch { D(args) => e }
-- comatch { D(args)[k] => (compile e) >> k }
compile (Comatch _ cocases) =
  let
    nominalStructural = case cocases of
      [] -> Structural
      ((MkACase _ (MkXtorName ns _ ) _ _):_) -> ns
    compileComatchCase (MkACase _ xt args t) = MkSCase () xt (Twice (const Nothing <$> args) [Nothing]) $ Apply () (compile t) (BoundVar () CnsRep (0,0))
  in
    XMatch () PrdRep nominalStructural $ compileComatchCase <$> cocases



compileSCase :: SCase ext -> SCase Compiled
compileSCase (MkSCase _ xt args cmd) = MkSCase () xt args (compileCmd cmd)

compileCmd :: Command ext -> Command Compiled
compileCmd (Apply _ prd cns) = Apply () (compile prd) (compile cns)
compileCmd (Print _ prd) = Print () (compile prd)
compileCmd (Done _) = Done ()

---------------------------------------------------------------------------------
-- Translate Program
---------------------------------------------------------------------------------

compileDecl :: Declaration ext -> Declaration Compiled
compileDecl (PrdCnsDecl _ pc isRec fv annot tm) = PrdCnsDecl () pc isRec fv annot (compile tm)
compileDecl (CmdDecl _ fv cmd)                  = CmdDecl () fv (compileCmd cmd)
compileDecl (DataDecl _ decl)                   = DataDecl () decl
compileDecl (ImportDecl _ mn)                   = ImportDecl () mn
compileDecl (SetDecl _ txt)                     = SetDecl () txt
compileDecl ParseErrorDecl                      = ParseErrorDecl   

compileProgram :: Program ext -> Program Compiled
compileProgram ps = compileDecl <$> ps

