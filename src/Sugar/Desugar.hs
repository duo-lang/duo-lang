module Sugar.Desugar ( Desugar(..) ) where

import Syntax.Core.Annot qualified as Core
import Syntax.Core.Program qualified as Core
import Syntax.Core.Terms qualified as Core
import Syntax.CST.Types (PrdCnsRep(..))
import Syntax.RST.Program qualified as RST
import Syntax.RST.Terms qualified as RST
import Sugar.Core qualified as Core

---------------------------------------------------------------------------------
-- The desugaring typeclass
---------------------------------------------------------------------------------

-- | Typeclass for desugaring.
-- The `Desugar` typeclass implements two operations, `desugar` and `embedCore`
-- which form an isomorphism between RST.X and Core.X objects.
-- For this reason, in a declaration `Desugar a b`, `a` uniquely determines `b`
-- and `b` uniquely determines `a`.
class Desugar a b | a -> b, b -> a where
  -- | An operation going from a RST.X object to a Core.X object.
  -- The inverse of `desugar` is `embedCore`.
  desugar :: a -> b
  -- | An operation going from a Core.X object to a RST.X object.
  -- The inverse of `embedCore` is `desugar`.
  embedCore :: b -> a

---------------------------------------------------------------------------------
-- Implementation of `Desugar` for patterns and cases
---------------------------------------------------------------------------------

instance Desugar RST.Pattern Core.Pattern where
  desugar :: RST.Pattern -> Core.Pattern
  desugar (RST.XtorPat loc xt args) = Core.XtorPat loc xt args

  embedCore :: Core.Pattern -> RST.Pattern
  embedCore (Core.XtorPat loc xt args) = RST.XtorPat loc xt args

instance Desugar RST.PatternI Core.PatternI where
  desugar :: RST.PatternI -> Core.PatternI
  desugar (RST.XtorPatI loc xt args) = Core.XtorPatI loc xt args

  embedCore :: Core.PatternI -> RST.PatternI
  embedCore (Core.XtorPatI loc xt args) = RST.XtorPatI loc xt args

instance Desugar RST.CmdCase Core.CmdCase where
  desugar :: RST.CmdCase -> Core.CmdCase
  desugar (RST.MkCmdCase { cmdcase_loc, cmdcase_pat, cmdcase_cmd }) =
    Core.MkCmdCase { cmdcase_loc = cmdcase_loc
                   , cmdcase_pat = desugar cmdcase_pat
                   , cmdcase_cmd = desugar cmdcase_cmd
                   }

  embedCore :: Core.CmdCase -> RST.CmdCase
  embedCore Core.MkCmdCase { cmdcase_loc, cmdcase_pat, cmdcase_cmd } =
    RST.MkCmdCase { cmdcase_loc = cmdcase_loc
                  , cmdcase_pat = embedCore cmdcase_pat
                  , cmdcase_cmd = embedCore cmdcase_cmd
                  }

instance Desugar (RST.TermCase pc) (Core.TermCase pc) where
  desugar :: RST.TermCase pc -> Core.TermCase pc
  desugar (RST.MkTermCase loc pat t) =
    Core.MkTermCase loc (desugar pat) (desugar t)

  embedCore :: Core.TermCase pc -> RST.TermCase pc
  embedCore (Core.MkTermCase loc pat t) =
    RST.MkTermCase loc (embedCore pat) (embedCore t)



instance Desugar (RST.TermCaseI pc) (Core.TermCaseI pc) where
  desugar :: RST.TermCaseI pc -> Core.TermCaseI pc
  desugar (RST.MkTermCaseI loc pati t) =
    Core.MkTermCaseI loc (desugar pati) (desugar t)

  embedCore :: Core.TermCaseI pc -> RST.TermCaseI pc
  embedCore (Core.MkTermCaseI loc pati t) =
    RST.MkTermCaseI loc (embedCore pati) (embedCore t)

instance Desugar RST.InstanceCase Core.InstanceCase where
  desugar :: RST.InstanceCase -> Core.InstanceCase
  desugar RST.MkInstanceCase { instancecase_loc, instancecase_pat, instancecase_cmd } =
    Core.MkInstanceCase { instancecase_loc = instancecase_loc
                        , instancecase_pat = desugar instancecase_pat
                        , instancecase_cmd = desugar instancecase_cmd
                        }

  embedCore :: Core.InstanceCase -> RST.InstanceCase
  embedCore Core.MkInstanceCase { instancecase_loc, instancecase_pat, instancecase_cmd } =
    RST.MkInstanceCase { instancecase_loc = instancecase_loc
                       , instancecase_pat = embedCore instancecase_pat
                       , instancecase_cmd = embedCore instancecase_cmd
                       }


---------------------------------------------------------------------------------
-- Implementation of `Desugar` for terms
---------------------------------------------------------------------------------

instance Desugar RST.PrdCnsTerm Core.PrdCnsTerm where
  desugar :: RST.PrdCnsTerm -> Core.PrdCnsTerm
  desugar (RST.PrdTerm tm) = Core.PrdTerm (desugar tm)
  desugar (RST.CnsTerm tm) = Core.CnsTerm (desugar tm)

  embedCore :: Core.PrdCnsTerm -> RST.PrdCnsTerm
  embedCore (Core.PrdTerm tm) = RST.PrdTerm (embedCore tm)
  embedCore (Core.CnsTerm tm) = RST.CnsTerm (embedCore tm)

instance Desugar RST.Substitution Core.Substitution where
  desugar :: RST.Substitution -> Core.Substitution
  desugar (RST.MkSubstitution subst) = Core.MkSubstitution $ fmap desugar subst

  embedCore :: Core.Substitution -> RST.Substitution
  embedCore (Core.MkSubstitution subst) = RST.MkSubstitution (fmap embedCore subst)

instance Desugar (RST.SubstitutionI pc) (Core.SubstitutionI pc) where
  desugar :: RST.SubstitutionI pc -> Core.SubstitutionI pc
  desugar (RST.MkSubstitutionI (subst1, pc, subst2)) = 
    Core.MkSubstitutionI (desugar <$> subst1, pc, desugar <$> subst2)

  embedCore :: Core.SubstitutionI pc -> RST.SubstitutionI pc
  embedCore (Core.MkSubstitutionI (subst1, pc, subst2)) =
    RST.MkSubstitutionI (embedCore <$> subst1, pc, embedCore <$> subst2)

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
    Core.Xtor loc Core.XtorAnnotOrig pc ns xt (desugar args)
  desugar (RST.MuAbs loc pc  bs cmd) =
    Core.MuAbs loc Core.MuAnnotOrig pc bs (desugar cmd)
  desugar (RST.XCase loc pc ns cases) =
    Core.XCase loc Core.MatchAnnotOrig pc ns (desugar <$> cases)
  ---------------------------------------------------------------------------------
  -- Syntactic sugar
  ---------------------------------------------------------------------------------
  desugar (RST.Semi loc rep ns xt subst t) =
    Core.Semi loc rep ns xt (desugar subst) (desugar t)
  desugar (RST.Dtor loc rep ns xt t subst) =
    Core.Dtor loc rep ns xt (desugar t) (desugar subst)
  desugar (RST.CaseOf loc rep ns t cases) =
    Core.CaseOf loc rep ns (desugar t) (desugar <$> cases)
  desugar (RST.CocaseOf loc rep ns t cases) =
    Core.CocaseOf loc rep ns (desugar t) (desugar <$> cases)
  desugar (RST.CaseI loc rep ns tmcasesI) =
    Core.XCaseI loc rep CnsRep ns (desugar <$> tmcasesI)
  desugar (RST.CocaseI loc rep ns cocases) =
    Core.XCaseI loc rep PrdRep ns (desugar <$> cocases)
  desugar (RST.Lambda loc pc fv tm) =
    Core.Lambda loc pc fv (desugar tm)
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

  embedCore :: Core.Term pc -> RST.Term pc
  ---------------------------------------------------------------------------------
  -- Core constructs
  ---------------------------------------------------------------------------------
  embedCore (Core.BoundVar loc rep idx) =
    RST.BoundVar loc rep idx
  embedCore (Core.FreeVar loc rep idx) =
    RST.FreeVar loc rep idx
  embedCore (Core.RawXtor loc rep ns xs subst) =
    RST.Xtor loc rep ns xs (embedCore subst)
  embedCore (Core.RawMuAbs loc rep b cmd) =
    RST.MuAbs loc rep b (embedCore cmd)
  embedCore (Core.RawCase loc rep ns cases) =
    RST.XCase loc rep ns (embedCore <$> cases)
  ---------------------------------------------------------------------------------
  -- Syntactic sugar
  ---------------------------------------------------------------------------------
  embedCore (Core.Semi loc rep ns xt subst t ) =
    RST.Semi loc rep ns xt (embedCore subst) (embedCore t)
  embedCore (Core.Dtor loc rep ns xt t subst) =
    RST.Dtor loc rep ns xt (embedCore t) (embedCore subst)
  embedCore (Core.CaseOf loc rep ns t cases) =
    RST.CaseOf loc rep ns (embedCore t) (embedCore <$> cases)
  embedCore (Core.CocaseOf loc rep ns t cases) =
    RST.CocaseOf loc rep ns (embedCore t) (embedCore <$> cases)
  embedCore (Core.XCaseI loc rep CnsRep ns cases) =
    RST.CaseI loc rep ns (embedCore <$> cases)
  embedCore (Core.XCaseI loc rep PrdRep ns cases) =
    RST.CocaseI loc rep ns (embedCore <$> cases)
  embedCore (Core.Lambda loc rep fv tm) =
    RST.Lambda loc rep fv (embedCore tm)
  embedCore (Core.XCase loc _ pc ns cases) =
    RST.XCase loc pc ns (embedCore <$> cases) -- revisit
  ---------------------------------------------------------------------------------
  -- Primitive constructs
  ---------------------------------------------------------------------------------
  embedCore (Core.PrimLitI64 loc d) =
    RST.PrimLitI64 loc d
  embedCore (Core.PrimLitF64 loc d) =
    RST.PrimLitF64 loc d
  embedCore (Core.PrimLitChar loc d) =
    RST.PrimLitChar loc d
  embedCore (Core.PrimLitString loc d) =
    RST.PrimLitString loc d


instance Desugar RST.Command Core.Command where
  desugar :: RST.Command -> Core.Command
  desugar (RST.Apply loc prd cns) =
    Core.Apply loc Core.ApplyAnnotOrig (desugar prd) (desugar cns)
  desugar (RST.Print loc prd cmd) =
    Core.Print loc (desugar prd) (desugar cmd)
  desugar (RST.Read loc cns) =
    Core.Read loc (desugar cns)
  desugar (RST.Jump loc fv) =
    Core.Jump loc fv
  desugar (RST.Method loc mn cn subst) =
    Core.Method loc mn cn (desugar subst)
  desugar (RST.ExitSuccess loc) =
    Core.ExitSuccess loc
  desugar (RST.ExitFailure loc) =
    Core.ExitFailure loc
  desugar (RST.PrimOp loc op subst) =
    Core.PrimOp loc op (desugar subst)
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

  embedCore :: Core.Command -> RST.Command
  embedCore (Core.RawApply loc prd cns ) =
    RST.Apply loc (embedCore prd) (embedCore cns)
  embedCore (Core.CocaseOfI loc rep ns t cases) =
    RST.CocaseOfI loc rep ns (embedCore t) (embedCore <$> cases)
  embedCore (Core.CaseOfI loc rep ns t cases) =
    RST.CaseOfI loc rep ns  (embedCore t) (embedCore <$> cases)
  embedCore (Core.CocaseOfCmd loc ns t cases) =
    RST.CocaseOfCmd loc ns (embedCore t) (embedCore <$> cases)
  embedCore (Core.CaseOfCmd loc ns t cases) =
    RST.CaseOfCmd loc ns (embedCore t) (embedCore <$> cases)
  embedCore (Core.Method loc mn cn subst) =
    RST.Method loc mn cn (embedCore subst)
  embedCore (Core.Print loc tm cmd) =
    RST.Print loc (embedCore tm) (embedCore cmd)
  embedCore (Core.Read loc tm) =
    RST.Read loc (embedCore tm)
  embedCore (Core.Jump loc fv) =
    RST.Jump loc fv
  embedCore (Core.ExitSuccess loc) =
    RST.ExitSuccess loc
  embedCore (Core.ExitFailure loc) =
    RST.ExitFailure loc
  embedCore (Core.PrimOp loc op subst) =
    RST.PrimOp loc op (embedCore subst)


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

  embedCore :: Core.PrdCnsDeclaration pc -> RST.PrdCnsDeclaration pc
  embedCore Core.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term } =
    RST.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                            , pcdecl_doc = pcdecl_doc
                            , pcdecl_pc = pcdecl_pc
                            , pcdecl_isRec = pcdecl_isRec
                            , pcdecl_name = pcdecl_name
                            , pcdecl_annot = pcdecl_annot
                            , pcdecl_term = embedCore pcdecl_term
                            }

instance Desugar RST.CommandDeclaration Core.CommandDeclaration where
  desugar :: RST.CommandDeclaration -> Core.CommandDeclaration
  desugar RST.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
    Core.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                              , cmddecl_doc = cmddecl_doc
                              , cmddecl_name = cmddecl_name
                              , cmddecl_cmd = desugar cmddecl_cmd
                              }

  embedCore :: Core.CommandDeclaration -> RST.CommandDeclaration
  embedCore Core.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } =
    RST.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                             , cmddecl_doc = cmddecl_doc
                             , cmddecl_name = cmddecl_name
                             , cmddecl_cmd = embedCore cmddecl_cmd
                             }

instance Desugar RST.InstanceDeclaration Core.InstanceDeclaration where
  desugar :: RST.InstanceDeclaration -> Core.InstanceDeclaration
  desugar RST.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_class, instancedecl_typ, instancedecl_cases } =
    Core.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                               , instancedecl_doc = instancedecl_doc
                               , instancedecl_class = instancedecl_class
                               , instancedecl_typ = instancedecl_typ
                               , instancedecl_cases = desugar <$> instancedecl_cases
                               }

  embedCore :: Core.InstanceDeclaration -> RST.InstanceDeclaration
  embedCore Core.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_class, instancedecl_typ, instancedecl_cases } =
    RST.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                              , instancedecl_doc = instancedecl_doc
                              , instancedecl_class = instancedecl_class
                              , instancedecl_typ = instancedecl_typ
                              , instancedecl_cases = embedCore <$> instancedecl_cases
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

  embedCore :: Core.Declaration -> RST.Declaration
  embedCore (Core.PrdCnsDecl pcrep decl) =
    RST.PrdCnsDecl pcrep (embedCore decl)
  embedCore (Core.CmdDecl decl) =
    RST.CmdDecl (embedCore decl)
  embedCore (Core.DataDecl decl) =
    RST.DataDecl decl
  embedCore (Core.XtorDecl decl) =
    RST.XtorDecl decl
  embedCore (Core.ImportDecl decl) =
    RST.ImportDecl decl
  embedCore (Core.SetDecl decl) =
    RST.SetDecl decl
  embedCore (Core.TyOpDecl decl) =
    RST.TyOpDecl decl
  embedCore (Core.TySynDecl decl) =
    RST.TySynDecl decl
  embedCore (Core.ClassDecl decl) =
    RST.ClassDecl decl
  embedCore (Core.InstanceDecl decl) =
    RST.InstanceDecl (embedCore decl)


instance Desugar RST.Module Core.Module where
  desugar :: RST.Module -> Core.Module
  desugar RST.MkModule { mod_name, mod_libpath, mod_decls } =
    Core.MkModule { mod_name = mod_name
                  , mod_libpath = mod_libpath
                  , mod_decls = desugar <$> mod_decls
                  }

  embedCore :: Core.Module -> RST.Module
  embedCore Core.MkModule { mod_name, mod_libpath, mod_decls } =
    RST.MkModule { mod_name = mod_name
                 , mod_libpath = mod_libpath
                 , mod_decls = embedCore <$> mod_decls
                 }
