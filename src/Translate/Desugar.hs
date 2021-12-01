module Translate.Desugar
  ( desugarTerm
  , desugarPCTerm
  , desugarProgram
  , desugarCmd
  , isDesugaredTerm
  , isDesugaredCommand
  )
  where

import Syntax.Terms
import Syntax.CommonTerm
import Syntax.Program ( Declaration(..), Program )

---------------------------------------------------------------------------------
-- Check if term is desugared
---------------------------------------------------------------------------------

isDesugaredPCTerm :: PrdCnsTerm Inferred -> Bool
isDesugaredPCTerm (PrdTerm tm) = isDesugaredTerm tm
isDesugaredPCTerm (CnsTerm tm) = isDesugaredTerm tm

isDesugaredTerm :: Term pc Inferred -> Bool
-- Core terms
isDesugaredTerm (BoundVar _ _ _) = True
isDesugaredTerm (FreeVar _ _ _) = True
isDesugaredTerm (XtorCall _ _ _ subst) = and (isDesugaredPCTerm <$> subst)
isDesugaredTerm (MuAbs _ _ _ cmd) = isDesugaredCommand cmd
isDesugaredTerm (XMatch _ _ _ cases) = and ((\MkCmdCase { cmdcase_cmd } -> isDesugaredCommand cmdcase_cmd ) <$> cases)
-- Non-core terms
isDesugaredTerm Dtor{} = False
isDesugaredTerm Match {} = False
isDesugaredTerm Comatch {} = False

isDesugaredCommand :: Command Inferred -> Bool
isDesugaredCommand (Apply _ prd cns) = isDesugaredTerm prd && isDesugaredTerm cns
isDesugaredCommand (Print _ prd) = isDesugaredTerm prd
isDesugaredCommand (Done _) = True

---------------------------------------------------------------------------------
-- Desugar Terms
--
-- This translates terms into the core subset of terms.
---------------------------------------------------------------------------------

resVar :: FreeVarName
resVar = "$result"


desugarPCTerm :: PrdCnsTerm Inferred -> PrdCnsTerm Compiled
desugarPCTerm (PrdTerm tm) = PrdTerm $ desugarTerm tm
desugarPCTerm (CnsTerm tm) = CnsTerm $ desugarTerm tm

desugarTerm :: Term pc Inferred -> Term pc Compiled
desugarTerm (BoundVar _ pc idx) = BoundVar () pc idx
desugarTerm (FreeVar _ pc fv) = FreeVar () pc fv
desugarTerm (XtorCall _ pc xt args) = XtorCall () pc xt (desugarPCTerm <$> args)
desugarTerm (MuAbs _ pc bs cmd) = MuAbs () pc bs (desugarCmd cmd)
desugarTerm (XMatch _ pc ns cases) = XMatch () pc ns (desugarCmdCase <$> cases)
-- we want to desugar e.D(args')
-- Mu k.[(desugar e) >> D (desugar <$> args')[k] ]
desugarTerm (Dtor _ xt t args) =
  let
    cmd = Apply () (desugarTerm t) (XtorCall () CnsRep xt $ (desugarPCTerm <$> args) ++ [CnsTerm $ FreeVar () CnsRep resVar])
  in
    MuAbs () PrdRep Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd cmd
-- we want to desugar match t { C (args) => e1 }
-- Mu k.[ (desugar t) >> match {C (args) => (desugar e1) >> k } ]
desugarTerm (Match _ ns t cases)   =
  let
    desugarMatchCase (MkACase _ xt args t) = MkCmdCase () xt [(Prd, Nothing) | _ <- args]  $ Apply () (desugarTerm t) (FreeVar () CnsRep resVar)
    cmd = Apply () (desugarTerm t) (XMatch () CnsRep ns  (desugarMatchCase <$> cases))
  in
    MuAbs () PrdRep Nothing $ commandClosing [(Cns, resVar)] $ shiftCmd cmd
-- we want to desugar comatch { D(args) => e }
-- comatch { D(args)[k] => (desugar e) >> k }
desugarTerm (Comatch _ ns cocases) =
  let
    desugarComatchCase (MkACase _ xt args t) = MkCmdCase () xt ([(Prd, Nothing) | _ <- args] ++ [(Cns,Nothing)]) $ Apply () (desugarTerm t) (BoundVar () CnsRep (0,length args))
  in
    XMatch () PrdRep ns $ desugarComatchCase <$> cocases


desugarCmdCase :: CmdCase Inferred -> CmdCase Compiled
desugarCmdCase (MkCmdCase _ xt args cmd) = MkCmdCase () xt args (desugarCmd cmd)

desugarCmd :: Command Inferred -> Command Compiled
desugarCmd (Apply _ prd cns) = Apply () (desugarTerm prd) (desugarTerm cns)
desugarCmd (Print _ prd) = Print () (desugarTerm prd)
desugarCmd (Done _) = Done ()

---------------------------------------------------------------------------------
-- Translate Program
---------------------------------------------------------------------------------

desugarDecl :: Declaration Inferred -> Declaration Compiled
desugarDecl (PrdCnsDecl _ pc isRec fv annot tm) = PrdCnsDecl () pc isRec fv annot (desugarTerm tm)
desugarDecl (CmdDecl _ fv cmd)                  = CmdDecl () fv (desugarCmd cmd)
desugarDecl (DataDecl _ decl)                   = DataDecl () decl
desugarDecl (ImportDecl _ mn)                   = ImportDecl () mn
desugarDecl (SetDecl _ txt)                     = SetDecl () txt
desugarDecl ParseErrorDecl                      = ParseErrorDecl   

desugarProgram :: Program Inferred -> Program Compiled
desugarProgram ps = desugarDecl <$> ps

