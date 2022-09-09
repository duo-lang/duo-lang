{-# LANGUAGE FunctionalDependencies #-}
module Sugar.Desugar
  ( Desugar(..)
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

class Desugar a b | a -> b where
  desugar :: a -> b

instance Desugar RST.PrdCnsTerm Core.PrdCnsTerm where
  desugar :: RST.PrdCnsTerm -> Core.PrdCnsTerm
  desugar (RST.PrdTerm tm) = Core.PrdTerm $ desugar tm
  desugar (RST.CnsTerm tm) = Core.CnsTerm $ desugar tm

instance Desugar RST.Pattern Core.Pattern where
  desugar :: RST.Pattern -> Core.Pattern
  desugar (RST.XtorPat loc xt args) = Core.XtorPat loc xt args

instance Desugar (RST.Term pc) (Core.Term pc) where
  desugar :: RST.Term pc -> Core.Term pc
  ---------------------------------------------------------------------------------
  -- Core constructs
  ---------------------------------------------------------------------------------
  desugar (RST.BoundVar loc pc  idx) =
    Core.BoundVar loc pc idx
  desugar (RST.FreeVar loc pc fv) =
    Core.FreeVar loc pc fv
  desugar (RST.Xtor loc pc ns xt args) =
    Core.Xtor loc XtorAnnotOrig pc ns xt (desugar <$> args)
  desugar (RST.MuAbs loc pc  bs cmd) =
    Core.MuAbs loc MuAnnotOrig pc bs (desugar cmd)
  desugar (RST.XCase loc pc ns cases) =
    Core.XCase loc MatchAnnotOrig pc ns (desugar <$> cases)
  ---------------------------------------------------------------------------------
  -- Syntactic sugar
  ---------------------------------------------------------------------------------
  desugar (RST.Semi loc rep ns xt (args1,r,args2) t) = Core.Semi loc rep ns xt (desugar <$> args1,r,desugar <$> args2) (desugar t)
  desugar (RST.Dtor loc rep ns xt t (args1,r,args2)) = Core.Dtor loc rep ns xt (desugar t) (desugar <$> args1,r,desugar <$> args2)
  desugar (RST.CaseOf loc rep ns t cases) = Core.CaseOf loc rep ns (desugar t) (desugar <$> cases)
  desugar (RST.CocaseOf loc rep ns t cases) = Core.CocaseOf loc rep ns (desugar t) (desugar <$> cases)
  desugar (RST.CaseI loc rep ns tmcasesI) = Core.XCaseI loc rep CnsRep ns (desugar <$> tmcasesI)
  desugar (RST.CocaseI loc rep ns cocases) = Core.XCaseI loc rep PrdRep ns (desugar <$> cocases)
  desugar (RST.Lambda loc pc fv tm) = Core.Lambda loc pc fv (desugar tm)

  ---------------------------------------------------------------------------------
  -- Primitive constructs
  ---------------------------------------------------------------------------------
  desugar (RST.PrimLitI64 loc i) =
    Core.PrimLitI64 loc i
  desugar (RST.PrimLitF64 loc d) =
    Core.PrimLitF64 loc d
  desugar (RST.PrimLitChar loc d) =
    Core.PrimLitChar loc d
  desugar (RST.PrimLitString loc d) =
    Core.PrimLitString loc d

instance Desugar RST.CmdCase Core.CmdCase where
  desugar :: RST.CmdCase -> Core.CmdCase
  desugar (RST.MkCmdCase loc pat cmd) =
    Core.MkCmdCase loc (desugar pat) (desugar cmd)

instance Desugar RST.InstanceCase Core.InstanceCase where
  desugar :: RST.InstanceCase -> Core.InstanceCase
  desugar (RST.MkInstanceCase loc pat cmd) =
    Core.MkInstanceCase loc (desugar pat) (desugar cmd)

instance Desugar (RST.TermCaseI pc) (Core.TermCaseI pc) where
  desugar :: RST.TermCaseI pc -> Core.TermCaseI pc
  desugar (RST.MkTermCaseI loc pti t) = Core.MkTermCaseI loc (desugar pti) (desugar t)

instance Desugar RST.PatternI Core.PatternI where
  desugar :: RST.PatternI -> Core.PatternI
  desugar (RST.XtorPatI loc xt args) = Core.XtorPatI loc xt args

instance Desugar (RST.TermCase pc) (Core.TermCase pc) where
  desugar :: RST.TermCase pc -> Core.TermCase pc
  desugar (RST.MkTermCase loc pat t) = Core.MkTermCase loc (desugar pat) (desugar t)

instance Desugar RST.Command Core.Command where
  desugar :: RST.Command -> Core.Command
  desugar (RST.Apply loc prd cns) =
    Core.Apply loc ApplyAnnotOrig (desugar prd) (desugar cns)
  desugar (RST.Print loc prd cmd) =
    Core.Print loc (desugar prd) (desugar cmd)
  desugar (RST.Read loc cns) =
    Core.Read loc (desugar cns)
  desugar (RST.Jump loc fv) =
    Core.Jump loc fv
  desugar (RST.Method loc mn cn subst) =
    Core.Method loc mn cn (desugar <$> subst)
  desugar (RST.ExitSuccess loc) =
    Core.ExitSuccess loc
  desugar (RST.ExitFailure loc) =
    Core.ExitFailure loc
  desugar (RST.PrimOp loc op subst) =
    Core.PrimOp loc op (desugar <$> subst)
  ---------------------------------------------------------------------------------
  -- Syntactic sugar
  -- uses pattern synonyms defined in Sugar.Core 
  ---------------------------------------------------------------------------------
  desugar (RST.CaseOfCmd loc ns t cases) =
    Core.CaseOfCmd loc ns (desugar t) (desugar <$> cases)
  desugar (RST.CocaseOfCmd loc ns t cases) =
    Core.CocaseOfCmd loc ns (desugar t) (desugar <$> cases)
  desugar (RST.CaseOfI loc rep ns t cases) =
    Core.CaseOfI loc rep ns (desugar t) (desugar  <$> cases )
  desugar (RST.CocaseOfI loc rep ns t cases) =
    Core.CocaseOfI loc rep ns (desugar t) (desugar  <$> cases )

---------------------------------------------------------------------------------
-- Translate Program
---------------------------------------------------------------------------------

instance Desugar (RST.PrdCnsDeclaration pc) (Core.PrdCnsDeclaration pc) where
  desugar :: RST.PrdCnsDeclaration pc -> Core.PrdCnsDeclaration pc
  desugar RST.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term} =
    Core.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                            , pcdecl_doc = pcdecl_doc
                            , pcdecl_pc = pcdecl_pc
                            , pcdecl_isRec = pcdecl_isRec
                            , pcdecl_name = pcdecl_name
                            , pcdecl_annot = pcdecl_annot
                            , pcdecl_term = desugar pcdecl_term
                            }

instance Desugar RST.CommandDeclaration Core.CommandDeclaration where
  desugar :: RST.CommandDeclaration -> Core.CommandDeclaration
  desugar RST.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
    Core.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                              , cmddecl_doc = cmddecl_doc
                              , cmddecl_name = cmddecl_name
                              , cmddecl_cmd = desugar cmddecl_cmd
                              }

instance Desugar RST.InstanceDeclaration Core.InstanceDeclaration where
  desugar :: RST.InstanceDeclaration -> Core.InstanceDeclaration
  desugar RST.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases } =
      Core.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                                , instancedecl_doc = instancedecl_doc
                                , instancedecl_name = instancedecl_name
                                , instancedecl_typ = instancedecl_typ
                                , instancedecl_cases = desugar <$> instancedecl_cases
                                }

instance Desugar RST.Declaration Core.Declaration where
  desugar :: RST.Declaration -> Core.Declaration
  desugar (RST.PrdCnsDecl pcrep decl) =
    Core.PrdCnsDecl pcrep (desugar decl)
  desugar (RST.CmdDecl decl) =
    Core.CmdDecl (desugar decl)
  desugar (RST.DataDecl decl) =
    Core.DataDecl decl
  desugar (RST.XtorDecl decl) =
    Core.XtorDecl decl
  desugar (RST.ImportDecl decl) =
    Core.ImportDecl decl
  desugar (RST.SetDecl decl) =
    Core.SetDecl decl
  desugar (RST.TyOpDecl decl) =
    Core.TyOpDecl decl
  desugar (RST.TySynDecl decl) =
    Core.TySynDecl decl
  desugar (RST.ClassDecl decl) =
    Core.ClassDecl decl
  desugar (RST.InstanceDecl decl) =
    Core.InstanceDecl (desugar decl)

instance Desugar RST.Module Core.Module where
  desugar :: RST.Module -> Core.Module
  desugar RST.MkModule { mod_name, mod_fp, mod_decls } =
    Core.MkModule { mod_name = mod_name
                  , mod_fp = mod_fp
                  , mod_decls = desugar <$> mod_decls
                  }

-- should be resolved, since it's  not actually desugaring anything anymore
instance Desugar (Map ModuleName Environment) EvalEnv where
  desugar :: Map ModuleName Environment -> EvalEnv
  desugar map = fold $ desugar <$> M.elems map

instance Desugar Environment EvalEnv where
  desugar :: Environment -> EvalEnv
  desugar MkEnvironment { prdEnv, cnsEnv, cmdEnv } = (prd,cns,cmd)
    where
      prd = (\(tm,_,_) -> tm) <$> prdEnv
      cns = (\(tm,_,_) -> tm) <$> cnsEnv
      cmd = fst <$> cmdEnv
