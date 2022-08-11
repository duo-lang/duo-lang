module Pretty.Terms where

import Prettyprinter

import Pretty.Common ()
import Pretty.Pretty
import Syntax.TST.Terms qualified as TST
import Syntax.RST.Terms qualified as RST
import Syntax.Core.Terms qualified as Core
import Syntax.CST.Terms qualified as CST
import Syntax.Common.Names ( FreeVarName )
import Translate.Embed
import Translate.Reparse

---------------------------------------------------------------------------------
-- Data/Codata and Nominal/Structural/Refinement
---------------------------------------------------------------------------------

instance PrettyAnn CST.NominalStructural where
  prettyAnn CST.Nominal = "Nominal"
  prettyAnn CST.Structural = "Structural"
  prettyAnn CST.Refinement = "Refinement"

---------------------------------------------------------------------------------
-- Patterns
---------------------------------------------------------------------------------

instance PrettyAnn CST.Pattern where
  prettyAnn (CST.PatXtor _ xt args) =
    prettyAnn xt <>
    parens (intercalateComma (map prettyAnn args))
  prettyAnn (CST.PatVar _ var) =
    prettyAnn var
  prettyAnn (CST.PatStar _) =
    annSymbol "*"
  prettyAnn (CST.PatWildcard _) =
    annSymbol "_"

---------------------------------------------------------------------------------
-- Pattern match cases and cocases
---------------------------------------------------------------------------------

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

instance PrettyAnn CST.TermOrStar  where
  prettyAnn (CST.ToSTerm t) = prettyAnn t
  prettyAnn CST.ToSStar  = "*"

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
  prettyAnn (CST.PrimLitChar _ f) =
    annLiteral (prettyAnn ("'" ++ (f : "'")))
  prettyAnn (CST.PrimLitString _ f) =
    annLiteral (prettyAnn ("\"" ++ f ++  "\""))
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
  prettyAnn (CST.NatLit _ CST.Structural n) =
    prettyAnn ("'" :: String) <> prettyAnn (show n)
  prettyAnn (CST.NatLit _ CST.Nominal n) =
    prettyAnn (show n)
  prettyAnn (CST.NatLit _ CST.Refinement n) =
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
  prettyAnn (CST.PrimCmdTerm (CST.PrimOp _ op subst)) =
    annKeyword (prettyAnn op) <>
    parens' comma (prettyAnn <$> subst)

---------------------------------------------------------------------------------
-- Primitives
---------------------------------------------------------------------------------

instance PrettyAnn CST.PrimitiveOp where
  prettyAnn CST.I64Add = "Add#I64"
  prettyAnn CST.I64Sub = "Sub#I64"
  prettyAnn CST.I64Mul = "Mul#I64"
  prettyAnn CST.I64Div = "Div#I64"
  prettyAnn CST.I64Mod = "Mod#I64"
  -- F64 Ops
  prettyAnn CST.F64Add = "Add#F64"
  prettyAnn CST.F64Sub = "Sub#F64"
  prettyAnn CST.F64Mul = "Mul#F64"
  prettyAnn CST.F64Div = "Div#F64"
  -- Char Ops
  prettyAnn CST.CharPrepend = "Prepend#Char"
  -- String Ops
  prettyAnn CST.StringAppend = "Append#String"

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

instance PrettyAnn TST.Command where
  prettyAnn cmd = prettyAnn (embedTSTCommand cmd)

instance PrettyAnn RST.Command where
  prettyAnn cmd = prettyAnn (reparseCommand cmd)

instance PrettyAnn Core.Command where
  prettyAnn cmd = prettyAnn (embedCoreCommand cmd)
