module Sugar.Desugar
  ( desugarTerm
  , desugarPCTerm
  , desugarPrdCnsDeclaration
  , desugarCommandDeclaration
  , desugarProgram
  , desugarCmd
  , desugarEnvironment
  , desugarDecl
  )
  where

import Data.Foldable (fold)
import Data.Map (Map)
import Data.Map qualified as M
import Driver.Environment (Environment(..))
import Eval.Definition (EvalEnv)
import Syntax.RST.Program qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.Core.Program qualified as Core
import Syntax.Core.Terms qualified as Core
import Syntax.CST.Types (PrdCnsRep(..))
import Syntax.CST.Names
import Syntax.Core.Annot
import qualified Sugar.Core as Core


---------------------------------------------------------------------------------
-- Desugar Terms
--
-- This translates terms into the core subset of terms.
---------------------------------------------------------------------------------

desugarPCTerm :: RST.PrdCnsTerm -> Core.PrdCnsTerm
desugarPCTerm (RST.PrdTerm tm) = Core.PrdTerm $ desugarTerm tm
desugarPCTerm (RST.CnsTerm tm) = Core.CnsTerm $ desugarTerm tm

desugarPat :: RST.Pattern -> Core.Pattern
desugarPat (RST.XtorPat loc xt args) = Core.XtorPat loc xt args

desugarTerm :: RST.Term pc -> Core.Term pc
---------------------------------------------------------------------------------
-- Core constructs
---------------------------------------------------------------------------------
desugarTerm (RST.BoundVar loc pc  idx) =
  Core.BoundVar loc pc idx
desugarTerm (RST.FreeVar loc pc fv) =
  Core.FreeVar loc pc fv
desugarTerm (RST.Xtor loc pc ns xt args) =
  Core.Xtor loc XtorAnnotOrig pc ns xt (desugarPCTerm <$> args)
desugarTerm (RST.MuAbs loc pc  bs cmd) =
  Core.MuAbs loc MuAnnotOrig pc bs (desugarCmd cmd)
desugarTerm (RST.XCase loc pc ns cases) =
  Core.XCase loc MatchAnnotOrig pc ns (desugarCmdCase <$> cases)
---------------------------------------------------------------------------------
-- Syntactic sugar
---------------------------------------------------------------------------------
desugarTerm (RST.Semi loc rep ns xt (args1,r,args2) t) = Core.Semi loc rep ns xt (desugarPCTerm <$> args1,r,desugarPCTerm <$> args2) (desugarTerm t)
desugarTerm (RST.Dtor loc rep ns xt t (args1,r,args2)) = Core.Dtor loc rep ns xt (desugarTerm t) (desugarPCTerm <$> args1,r,desugarPCTerm <$> args2)
desugarTerm (RST.CaseOf loc rep ns t cases) = Core.CaseOf loc rep ns (desugarTerm t) (desugarTermCase <$> cases)
desugarTerm (RST.CocaseOf loc rep ns t cases) = Core.CocaseOf loc rep ns (desugarTerm t) (desugarTermCase <$> cases)
desugarTerm (RST.CaseI loc rep ns tmcasesI) = Core.XCaseI loc rep CnsRep ns (desugarTermCaseI <$> tmcasesI)
desugarTerm (RST.CocaseI loc rep ns cocases) = Core.XCaseI loc rep PrdRep ns (desugarTermCaseI <$> cocases)
desugarTerm (RST.Lambda loc pc fv tm) = Core.Lambda loc pc fv (desugarTerm tm)

---------------------------------------------------------------------------------
-- Primitive constructs
---------------------------------------------------------------------------------
desugarTerm (RST.PrimLitI64 loc i) =
  Core.PrimLitI64 loc i
desugarTerm (RST.PrimLitF64 loc d) =
  Core.PrimLitF64 loc d
desugarTerm (RST.PrimLitChar loc d) =
  Core.PrimLitChar loc d
desugarTerm (RST.PrimLitString loc d) =
  Core.PrimLitString loc d

desugarCmdCase :: RST.CmdCase -> Core.CmdCase
desugarCmdCase (RST.MkCmdCase loc pat cmd) =
  Core.MkCmdCase loc (desugarPat pat) (desugarCmd cmd)

desugarInstanceCase :: RST.InstanceCase -> Core.InstanceCase
desugarInstanceCase (RST.MkInstanceCase loc pat cmd) =
  Core.MkInstanceCase loc (desugarPat pat) (desugarCmd cmd)

desugarTermCaseI :: RST.TermCaseI pc -> Core.TermCaseI pc
desugarTermCaseI (RST.MkTermCaseI loc pti t) = Core.MkTermCaseI loc (desugarPatI pti) (desugarTerm t)

desugarPatI :: RST.PatternI -> Core.PatternI
desugarPatI (RST.XtorPatI loc xt args) = Core.XtorPatI loc xt args

desugarTermCase :: RST.TermCase pc -> Core.TermCase pc
desugarTermCase (RST.MkTermCase loc pat t) = Core.MkTermCase loc (desugarPat pat) (desugarTerm t)

desugarCmd :: RST.Command -> Core.Command
desugarCmd (RST.Apply loc prd cns) =
  Core.Apply loc ApplyAnnotOrig (desugarTerm prd) (desugarTerm cns)
desugarCmd (RST.Print loc prd cmd) =
  Core.Print loc (desugarTerm prd) (desugarCmd cmd)
desugarCmd (RST.Read loc cns) =
  Core.Read loc (desugarTerm cns)
desugarCmd (RST.Jump loc fv) =
  Core.Jump loc fv
desugarCmd (RST.Method loc mn cn subst) =
  Core.Method loc mn cn (desugarPCTerm <$> subst)
desugarCmd (RST.ExitSuccess loc) =
  Core.ExitSuccess loc
desugarCmd (RST.ExitFailure loc) =
  Core.ExitFailure loc
desugarCmd (RST.PrimOp loc op subst) =
  Core.PrimOp loc op (desugarPCTerm <$> subst)
---------------------------------------------------------------------------------
-- Syntactic sugar
-- uses pattern synonyms defined in Sugar.Core 
---------------------------------------------------------------------------------

desugarCmd (RST.CaseOfCmd loc ns t cases) =
  Core.CaseOfCmd loc ns (desugarTerm t) (desugarCmdCase <$> cases)
desugarCmd (RST.CocaseOfCmd loc ns t cases) =
  Core.CocaseOfCmd loc ns (desugarTerm t) (desugarCmdCase <$> cases)
desugarCmd (RST.CaseOfI loc rep ns t cases) =
  Core.CaseOfI loc rep ns (desugarTerm t) (desugarTermCaseI  <$> cases )
desugarCmd (RST.CocaseOfI loc rep ns t cases) =
  Core.CocaseOfI loc rep ns (desugarTerm t) (desugarTermCaseI  <$> cases )

---------------------------------------------------------------------------------
-- Translate Program
---------------------------------------------------------------------------------

desugarPrdCnsDeclaration :: RST.PrdCnsDeclaration pc -> Core.PrdCnsDeclaration pc
desugarPrdCnsDeclaration RST.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term} =
  Core.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                           , pcdecl_doc = pcdecl_doc
                           , pcdecl_pc = pcdecl_pc
                           , pcdecl_isRec = pcdecl_isRec
                           , pcdecl_name = pcdecl_name
                           , pcdecl_annot = pcdecl_annot
                           , pcdecl_term = desugarTerm pcdecl_term
                           }

desugarCommandDeclaration :: RST.CommandDeclaration -> Core.CommandDeclaration
desugarCommandDeclaration RST.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
  Core.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                            , cmddecl_doc = cmddecl_doc
                            , cmddecl_name = cmddecl_name
                            , cmddecl_cmd = desugarCmd cmddecl_cmd
                            }

desugarInstanceDeclaration :: RST.InstanceDeclaration -> Core.InstanceDeclaration
desugarInstanceDeclaration RST.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases } =
    Core.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                               , instancedecl_doc = instancedecl_doc
                               , instancedecl_name = instancedecl_name
                               , instancedecl_typ = instancedecl_typ
                               , instancedecl_cases = desugarInstanceCase <$> instancedecl_cases
                               }

desugarDecl :: RST.Declaration -> Core.Declaration
desugarDecl (RST.PrdCnsDecl pcrep decl) =
  Core.PrdCnsDecl pcrep (desugarPrdCnsDeclaration decl)
desugarDecl (RST.CmdDecl decl) =
  Core.CmdDecl (desugarCommandDeclaration decl)
desugarDecl (RST.DataDecl decl) =
  Core.DataDecl decl
desugarDecl (RST.XtorDecl decl) =
  Core.XtorDecl decl
desugarDecl (RST.ImportDecl decl) =
  Core.ImportDecl decl
desugarDecl (RST.SetDecl decl) =
  Core.SetDecl decl
desugarDecl (RST.TyOpDecl decl) =
  Core.TyOpDecl decl
desugarDecl (RST.TySynDecl decl) =
  Core.TySynDecl decl
desugarDecl (RST.ClassDecl decl) =
  Core.ClassDecl decl
desugarDecl (RST.InstanceDecl decl) =
  Core.InstanceDecl (desugarInstanceDeclaration decl)

desugarProgram :: RST.Program -> Core.Program
desugarProgram ps = desugarDecl <$> ps

-- should be resolved, since it's  not actually desugaring anything anymore
desugarEnvironment :: Map ModuleName Environment -> EvalEnv
desugarEnvironment map = fold $ desugarEnvironment' <$> M.elems map

desugarEnvironment' :: Environment -> EvalEnv
desugarEnvironment' MkEnvironment { prdEnv, cnsEnv, cmdEnv } = (prd,cns,cmd)
  where
    prd = (\(tm,_,_) -> tm) <$> prdEnv
    cns = (\(tm,_,_) -> tm) <$> cnsEnv
    cmd = (\(cmd,_) -> cmd) <$> cmdEnv
