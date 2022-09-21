module Pretty.Terms where

import Prettyprinter

import Pretty.Common ()
import Pretty.Pretty
import Sugar.Desugar (Desugar(embedCore))
import Syntax.TST.Terms qualified as TST
import Syntax.RST.Terms qualified as RST
import Syntax.Core.Terms qualified as Core
import Syntax.CST.Terms qualified as CST
import Syntax.CST.Names ( FreeVarName )
import Translate.EmbedTST (EmbedTST(..))
import Resolution.Unresolve

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
  prettyAnn cmdcase = prettyAnn (embedCore cmdcase)

instance PrettyAnn TST.CmdCase where
  prettyAnn cmdcase = prettyAnn (embedTST cmdcase)

instance PrettyAnn RST.CmdCase where
  prettyAnn cmdcase = prettyAnn (reparse cmdcase)

-- TermCase

instance PrettyAnn (RST.TermCase pc) where
  prettyAnn termcase = prettyAnn (reparse termcase)

instance PrettyAnn CST.TermCase where
  prettyAnn CST.MkTermCase{ tmcase_pat, tmcase_term } =
      prettyAnn tmcase_pat <+>
      annSymbol "=>" <+>
      prettyAnn tmcase_term

instance PrettyAnn (RST.TermCaseI pc) where
  prettyAnn termcasei = prettyAnn (reparse termcasei)

instance PrettyAnn CST.TermOrStar  where
  prettyAnn (CST.ToSTerm t) = prettyAnn t
  prettyAnn CST.ToSStar  = "*"

---------------------------------------------------------------------------------
-- Substitutions
---------------------------------------------------------------------------------

-- PrdCnsTerm

instance PrettyAnn TST.PrdCnsTerm where
  prettyAnn pcterm = prettyAnn (embedCore (embedTST pcterm))

instance PrettyAnn RST.PrdCnsTerm where
  prettyAnn pcterm = prettyAnn (reparse pcterm)

-- Substitution

instance {-# OVERLAPPING #-} PrettyAnn TST.Substitution where
  prettyAnn subst = prettyAnn (embedCore (embedTST subst))

instance {-# OVERLAPPING #-} PrettyAnn RST.Substitution where
  prettyAnn subst = prettyAnn (reparse subst)

instance {-# OVERLAPPING #-} PrettyAnn CST.Substitution where
  prettyAnn subst = parens' comma (prettyAnn <$> subst)

-- SubstitutionI

instance PrettyAnn (RST.SubstitutionI pc) where
  prettyAnn substi = prettyAnn (reparse substi)

instance {-# OVERLAPPING #-} PrettyAnn CST.SubstitutionI where
  prettyAnn substi = parens' comma (prettyAnn <$> substi)


---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

instance PrettyAnn (TST.Term pc) where
  prettyAnn tm = prettyAnn (embedTST tm)

instance PrettyAnn (RST.Term pc) where
  prettyAnn tm = prettyAnn (reparse tm)

instance PrettyAnn (Core.Term pc) where
  prettyAnn tm = prettyAnn (embedCore tm)


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
  prettyAnn (CST.PrimTerm _ nm []) =
    prettyAnn nm
  prettyAnn (CST.PrimTerm _ nm args) =
    prettyAnn nm <>
    parens' comma (prettyAnn <$> args)
  prettyAnn (CST.Apply _ t1 t2) =
    group (nest 3 (line' <> vsep [parens $ prettyAnn t1, annSymbol ">>", prettyAnn t2]))

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

instance PrettyAnn TST.Command where
  prettyAnn cmd = prettyAnn (embedTST cmd)

instance PrettyAnn RST.Command where
  prettyAnn cmd = prettyAnn (reparse cmd)

instance PrettyAnn Core.Command where
  prettyAnn cmd = prettyAnn (embedCore cmd)
