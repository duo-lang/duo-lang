module Translate.Translate
  ( compile
  , compilePCTerm
  , compileProgram
  , compileCmd
  )
  where

import Syntax.Terms
import Syntax.CommonTerm
import Syntax.Program ( Declaration(..), Program )

---------------------------------------------------------------------------------
-- Translate Terms
---------------------------------------------------------------------------------

resVar :: FreeVarName
resVar = "$result"


compilePCTerm :: PrdCnsTerm Inferred -> PrdCnsTerm Compiled
compilePCTerm (PrdTerm tm) = PrdTerm $ compile tm
compilePCTerm (CnsTerm tm) = CnsTerm $ compile tm

compile :: Term pc Inferred -> Term pc Compiled
compile (BoundVar _ pc idx) = BoundVar () pc idx
compile (FreeVar _ pc fv) = FreeVar () pc fv
compile (XtorCall _ pc xt args) = XtorCall () pc xt (compilePCTerm <$> args)
compile (MuAbs _ pc bs cmd) = MuAbs () pc bs (compileCmd cmd)
compile (XMatch _ pc ns cases) = XMatch () pc ns (compileSCase <$> cases)
-- we want to compile e.D(args')
-- Mu k.[(compile e) >> D (compile <$> args')[k] ]
compile (Dtor _ xt t args) =
  let
    cmd = Apply () (compile t) (XtorCall () CnsRep xt $ (compilePCTerm <$> args) ++ [CnsTerm $ FreeVar () CnsRep resVar])
  in
    MuAbs () PrdRep Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd cmd
-- we want to compile match t { C (args) => e1 }
-- Mu k.[ (compile t) >> match {C (args) => (compile e1) >> k } ]
compile (Match _ ns t cases)   =
  let
    compileMatchCase (MkACase _ xt args t) = MkSCase () xt [(Prd, Nothing) | _ <- args]  $ Apply () (compile t) (FreeVar () CnsRep resVar)
    cmd = Apply () (compile t) (XMatch () CnsRep ns  (compileMatchCase <$> cases))
  in
    MuAbs () PrdRep Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd cmd
-- we want to compile comatch { D(args) => e }
-- comatch { D(args)[k] => (compile e) >> k }
compile (Comatch _ ns cocases) =
  let
    compileComatchCase (MkACase _ xt args t) = MkSCase () xt ([(Prd, Nothing) | _ <- args] ++ [(Cns,Nothing)]) $ Apply () (compile t) (BoundVar () CnsRep (0,length args))
  in
    XMatch () PrdRep ns $ compileComatchCase <$> cocases



compileSCase :: SCase Inferred -> SCase Compiled
compileSCase (MkSCase _ xt args cmd) = MkSCase () xt args (compileCmd cmd)

compileCmd :: Command Inferred -> Command Compiled
compileCmd (Apply _ prd cns) = Apply () (compile prd) (compile cns)
compileCmd (Print _ prd) = Print () (compile prd)
compileCmd (Done _) = Done ()

---------------------------------------------------------------------------------
-- Translate Program
---------------------------------------------------------------------------------

compileDecl :: Declaration Inferred -> Declaration Compiled
compileDecl (PrdCnsDecl _ pc isRec fv annot tm) = PrdCnsDecl () pc isRec fv annot (compile tm)
compileDecl (CmdDecl _ fv cmd)                  = CmdDecl () fv (compileCmd cmd)
compileDecl (DataDecl _ decl)                   = DataDecl () decl
compileDecl (ImportDecl _ mn)                   = ImportDecl () mn
compileDecl (SetDecl _ txt)                     = SetDecl () txt
compileDecl ParseErrorDecl                      = ParseErrorDecl   

compileProgram :: Program Inferred -> Program Compiled
compileProgram ps = compileDecl <$> ps

