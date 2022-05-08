module Pretty.Terms where

import Data.List.NonEmpty qualified as NE
import Prettyprinter

import Pretty.Common ()
import Pretty.Pretty
import Syntax.AST.Terms qualified as AST
import Syntax.RST.Terms qualified as RST
import Syntax.Core.Terms qualified as Core
import Syntax.CST.Terms qualified as CST
import Syntax.Common
import Sugar.Resugar
import Translate.ForgetTypes
import Translate.Reparse

---------------------------------------------------------------------------------
-- Pattern match cases and cocases
---------------------------------------------------------------------------------

-- Patterns

instance PrettyAnn CST.TermPat where
  prettyAnn (CST.XtorPat _ xt args) =
    prettyAnn xt <>
    parens (intercalateComma (map prettyAnn args))

-- CmdCase

instance PrettyAnn Core.CmdCase where
  prettyAnn cmdcase = prettyAnn (embedCmdCase cmdcase)

instance PrettyAnn AST.CmdCase where
  prettyAnn cmdcase = prettyAnn (forgetTypesCmdCase cmdcase)

instance PrettyAnn RST.CmdCase where
  prettyAnn cmdcase = prettyAnn (reparseCmdCase cmdcase)

-- TermCase

instance PrettyAnn (RST.TermCase pc) where
  prettyAnn termcase = prettyAnn (reparseTermCase termcase)

instance PrettyAnn CST.TermCase where
  prettyAnn CST.MkTermCase{ tmcase_pat, tmcase_term } =
      prettyAnn tmcase_pat <+>
      annSymbol "=>" <+>
      prettyAnn tmcase_term


instance PrettyAnn (RST.TermCaseI pc) where
  prettyAnn termcasei = prettyAnn (reparseTermCaseI termcasei)

instance PrettyAnn CST.FVOrStar where
  prettyAnn (CST.FoSFV v) = prettyAnn v
  prettyAnn CST.FoSStar = "*"

instance PrettyAnn CST.TermOrStar  where
  prettyAnn (CST.ToSTerm t) = prettyAnn t
  prettyAnn CST.ToSStar  = "*"

---------------------------------------------------------------------------------
-- Substitutions
---------------------------------------------------------------------------------

-- PrdCnsTerm

instance PrettyAnn AST.PrdCnsTerm where
  prettyAnn pcterm = prettyAnn (forgetTypesPCTerm pcterm)

instance PrettyAnn RST.PrdCnsTerm where
  prettyAnn pcterm = prettyAnn (reparsePCTerm pcterm)

-- Substitution

instance {-# OVERLAPPING #-} PrettyAnn AST.Substitution where
  prettyAnn subst = prettyAnn (forgetTypesSubst subst)

instance {-# OVERLAPPING #-} PrettyAnn RST.Substitution where
  prettyAnn subst = prettyAnn (reparseSubst subst)

instance {-# OVERLAPPING #-} PrettyAnn CST.Substitution where
  prettyAnn subst = parens' comma (prettyAnn <$> subst)

-- SubstitutionI

instance PrettyAnn (RST.SubstitutionI pc) where
  prettyAnn substi = prettyAnn (reparseSubstI substi)

instance {-# OVERLAPPING #-} PrettyAnn CST.SubstitutionI where
  prettyAnn substi = parens' comma (prettyAnn <$> substi)


---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

instance PrettyAnn (AST.Term pc) where
  prettyAnn tm = prettyAnn (forgetTypesTerm tm)

instance PrettyAnn (RST.Term pc) where
  prettyAnn tm = prettyAnn (reparseTerm tm)

instance PrettyAnn (Core.Term pc) where
  prettyAnn tm = prettyAnn (embedCoreTerm tm)

instance PrettyAnn CST.Term where
  prettyAnn (CST.Var _ v) =
    prettyAnn v
  prettyAnn (CST.Xtor _ xt args) =
    prettyAnn xt <>
    parens' comma (prettyAnn <$> args)
  prettyAnn (CST.Semi _ xt args c) =
    prettyAnn xt <>
    parens' comma (prettyAnn <$> args) <>
    annSymbol ";;" <+>
    prettyAnn c
  prettyAnn (CST.CocaseOf  _ t cases) =
    annKeyword "cocase" <+>
    prettyAnn t <+> annKeyword "of" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (CST.Cocase  _ cases) =
    annKeyword "cocase" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (CST.CaseOf  _ t cases) =
    annKeyword "case" <+>
    prettyAnn t <+> annKeyword "of" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (CST.Case  _ cases) =
    annKeyword "case" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (CST.MuAbs _ v cmd) =
    annKeyword "mu" <+>
    prettyAnn v <>
    "." <>
    parens (prettyAnn cmd)
  prettyAnn (CST.Dtor _ xt t substi) =
      parens ( prettyAnn t <> "." <> prettyAnn xt <> parens' comma (prettyAnn <$> substi))
  prettyAnn (CST.PrimLitI64 _ i) =
    annLiteral (prettyAnn i <>
    "#I64")
  prettyAnn (CST.PrimLitF64 _ f) =
    annLiteral (prettyAnn f <>
    "#F64")
  prettyAnn (CST.TermParens _ tm) =
    parens (prettyAnn tm)
  prettyAnn (CST.FunApp _ tm1 tm2) =
    prettyAnn tm1 <+>
    prettyAnn tm2
  prettyAnn (CST.MultiLambda _ vars tm) =
    annSymbol "\\" <>
    hsep (prettyAnn <$> vars) <+>
    annSymbol "=>" <+>
    prettyAnn tm
  prettyAnn (CST.Lambda _ var tm) =
    annSymbol "\\" <>
    prettyAnn var <+>
    annSymbol "=>" <+>
    prettyAnn tm
  prettyAnn (CST.NatLit _ Structural n) =
    prettyAnn ("'" :: String) <> prettyAnn (show n)
  prettyAnn (CST.NatLit _ Nominal n) =
    prettyAnn (show n)
  prettyAnn (CST.NatLit _ Refinement n) =
    prettyAnn (show n)
  prettyAnn (CST.DtorChain _ fst rst) =
    prettyAnn fst <>
    hsep (NE.toList ((\(xt,substi,_) -> annSymbol "." <> prettyAnn xt <> parens' comma (prettyAnn <$> substi)) <$> rst))
  prettyAnn (CST.PrimCmdTerm (CST.ExitSuccess _)) =
    annKeyword "ExitSuccess"
  prettyAnn (CST.PrimCmdTerm (CST.ExitFailure _)) =
    annKeyword "ExitFailure"
  prettyAnn (CST.PrimCmdTerm (CST.Print _ t cmd)) =
    annKeyword "Print" <>
    parens (prettyAnn t) <>
    semi <+>
    prettyAnn cmd
  prettyAnn (CST.PrimCmdTerm (CST.Read _ cns)) =
    annKeyword "Read" <>
    brackets (prettyAnn cns)
  prettyAnn (CST.Apply _ t1 t2) =
    group (nest 3 (line' <> vsep [parens $ prettyAnn t1, annSymbol ">>", prettyAnn t2]))
  prettyAnn (CST.PrimCmdTerm (CST.PrimOp _ pt op subst)) =
    annKeyword (prettyAnn (primOpKeyword op)) <>
    annTypeName (prettyAnn (primTypeKeyword pt)) <>
    parens' comma (prettyAnn <$> subst)

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

instance PrettyAnn AST.Command where
  prettyAnn cmd = prettyAnn (forgetTypesCommand cmd)

instance PrettyAnn RST.Command where
  prettyAnn cmd = prettyAnn (reparseCommand cmd)

instance PrettyAnn Core.Command where
  prettyAnn cmd = prettyAnn (embedCoreCommand cmd)
