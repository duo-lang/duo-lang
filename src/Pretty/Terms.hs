module Pretty.Terms where

import Prettyprinter

import Pretty.Common ()
import Pretty.Pretty
import Syntax.TST.Terms qualified as TST
import Syntax.RST.Terms qualified as RST
import Syntax.Core.Terms qualified as Core
import Syntax.CST.Terms qualified as CST
import Syntax.Common
import Translate.Embed
import Translate.Reparse

---------------------------------------------------------------------------------
-- Pattern match cases and cocases
---------------------------------------------------------------------------------

-- Patterns

instance PrettyAnn CST.TermPat where
  prettyAnn (CST.XtorPat _ xt args) =
    prettyAnn xt <>
    parens (intercalateComma (map prettyAnn args))

instance PrettyAnn CST.InstancePat where
  prettyAnn (CST.MethodPat _ m args) =
    prettyAnn m <>
    parens (intercalateComma (map prettyAnn args))

-- CmdCase

instance PrettyAnn Core.CmdCase where
  prettyAnn cmdcase = prettyAnn (embedCmdCase cmdcase)

instance PrettyAnn TST.CmdCase where
  prettyAnn cmdcase = prettyAnn (embedTSTCmdCase cmdcase)

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

-- InstanceCase

instance PrettyAnn (RST.InstanceCase pc) where
  prettyAnn instancecase = prettyAnn (reparseInstanceCase instancecase)

instance PrettyAnn CST.InstanceCase where
  prettyAnn CST.MkInstanceCase{ instancecase_pat, instancecase_term } =
      prettyAnn instancecase_pat <+>
      annSymbol "=>" <+>
      prettyAnn instancecase_term

---------------------------------------------------------------------------------
-- Substitutions
---------------------------------------------------------------------------------

-- PrdCnsTerm

instance PrettyAnn TST.PrdCnsTerm where
  prettyAnn pcterm = prettyAnn (embedPCTerm (embedTSTPCTerm pcterm))

instance PrettyAnn RST.PrdCnsTerm where
  prettyAnn pcterm = prettyAnn (reparsePCTerm pcterm)

-- Substitution

instance {-# OVERLAPPING #-} PrettyAnn TST.Substitution where
  prettyAnn subst = prettyAnn (embedSubst (embedTSTSubst subst))

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

instance PrettyAnn (TST.Term pc) where
  prettyAnn tm = prettyAnn (embedTSTTerm tm)

instance PrettyAnn (RST.Term pc) where
  prettyAnn tm = prettyAnn (reparseTerm tm)

instance PrettyAnn (Core.Term pc) where
  prettyAnn tm = prettyAnn (embedCoreTerm tm)


collectLambdaVarsAndBody ::  CST.Term -> ([FreeVarName], CST.Term)
collectLambdaVarsAndBody (CST.Lambda _ var tm) = (var:fvs,t)
  where (fvs, t) = collectLambdaVarsAndBody tm
collectLambdaVarsAndBody t = ([],t) 

collectCoLambdaVarsAndBody ::  CST.Term -> ([FreeVarName], CST.Term)
collectCoLambdaVarsAndBody (CST.CoLambda _ var tm) = (var:fvs,t)
  where (fvs, t) = collectCoLambdaVarsAndBody tm
collectCoLambdaVarsAndBody t = ([],t) 

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
    parens (prettyAnn tm1 <+> prettyAnn tm2)
  prettyAnn (CST.Lambda _ var tm) =
    let (params,body) = collectLambdaVarsAndBody tm in
    annSymbol "\\" <>
    hsep (prettyAnn <$> (var:params)) <+>
    annSymbol "=>" <+>
    prettyAnn body
  prettyAnn (CST.CoLambda _ var tm) =
    let (params,body) = collectCoLambdaVarsAndBody tm in
    annSymbol "\\" <>
    hsep (prettyAnn <$> (var:params)) <+>
    annSymbol "=<" <+>
    prettyAnn body
  prettyAnn (CST.NatLit _ Structural n) =
    prettyAnn ("'" :: String) <> prettyAnn (show n)
  prettyAnn (CST.NatLit _ Nominal n) =
    prettyAnn (show n)
  prettyAnn (CST.NatLit _ Refinement n) =
    prettyAnn (show n)
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

instance PrettyAnn TST.Command where
  prettyAnn cmd = prettyAnn (embedTSTCommand cmd)

instance PrettyAnn RST.Command where
  prettyAnn cmd = prettyAnn (reparseCommand cmd)

instance PrettyAnn Core.Command where
  prettyAnn cmd = prettyAnn (embedCoreCommand cmd)
