module Pretty.Terms where

import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NE
import Prettyprinter

import Pretty.Common ()
import Pretty.Pretty
import Syntax.AST.Terms qualified as AST
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Terms qualified as CST
import Syntax.Common
import Data.Bifunctor
import Translate.ForgetTypes
import Translate.Reparse

---------------------------------------------------------------------------------
-- Pattern match cases and cocases
---------------------------------------------------------------------------------

-- CmdCase

instance PrettyAnn AST.CmdCase where
  prettyAnn cmdcase = prettyAnn (forgetTypesCmdCase cmdcase)

instance PrettyAnn RST.CmdCase where
  prettyAnn cmdcase = prettyAnn (reparseCmdCase cmdcase)

instance PrettyAnn CST.CmdCase where
  prettyAnn CST.MkCmdCase { cmdcase_name, cmdcase_args, cmdcase_cmd } =
      prettyAnn cmdcase_name <>
      printCasesArgs cmdcase_args <+>
      annSymbol "=>" <+>
      prettyAnn cmdcase_cmd

-- TermCase

instance PrettyAnn (AST.TermCase pc) where
  prettyAnn termcase = prettyAnn (forgetTypesTermCase termcase)

instance PrettyAnn (RST.TermCase pc) where
  prettyAnn termcase = prettyAnn (reparseTermCase termcase)

instance PrettyAnn CST.TermCase where
  prettyAnn CST.MkTermCase{ tmcase_name, tmcase_args, tmcase_term } =
      prettyAnn tmcase_name <>
      printCasesArgs tmcase_args <+>
      annSymbol "=>" <+>
      prettyAnn tmcase_term

-- TermCaseI


instance PrettyAnn (AST.TermCaseI pc) where
  prettyAnn termcasei = prettyAnn (forgetTypesTermCaseI termcasei)

instance PrettyAnn (RST.TermCaseI pc) where
  prettyAnn termcasei = prettyAnn (reparseTermCaseI termcasei)

instance PrettyAnn CST.TermCaseI where
  prettyAnn CST.MkTermCaseI { tmcasei_name, tmcasei_args = (as1, (), as2), tmcasei_term } =
    prettyAnn tmcasei_name <>
    printCasesArgs as1 <>
    pretty ("[*]" :: String) <>
    printCasesArgs as2 <+>
    annSymbol "=>" <+>
    prettyAnn tmcasei_term

printCasesArgs :: [(PrdCns, FreeVarName)] -> Doc Annotation
printCasesArgs cs = printCasesArgs' (second (map snd) <$> splitOnChange fst cs)

printCasesArgs' :: [(PrdCns, [FreeVarName])] -> Doc Annotation
printCasesArgs' [] = mempty
printCasesArgs' ((Prd, vs) : cs) = parens (intercalateComma (map prettyAnn vs)) <> printCasesArgs' cs
printCasesArgs' ((Cns, vs) : cs) = brackets (intercalateComma (map prettyAnn vs)) <> printCasesArgs' cs

splitOnChange :: Eq b => (a -> b) -> [a] -> [(b, [a])]
splitOnChange _ [] = []
splitOnChange f (a : as) = helper f (f a) as [a] []
  where
    helper :: Eq b => (a -> b) -> b -> [a] -> [a] -> [(b, [a])] -> [(b, [a])]
    helper _ _ [] [] res = res
    helper _ prev [] curr res = res ++ [(prev, curr)]
    helper f prev (a : as) curr res | f a == prev = helper f prev as (curr ++ [a]) res
    helper f prev (a : as) curr res =
      helper f (f a) as [a] (res ++ [(prev, curr)])

---------------------------------------------------------------------------------
-- Substitutions
---------------------------------------------------------------------------------

-- PrdCnsTerm

instance PrettyAnn AST.PrdCnsTerm where
  prettyAnn pcterm = prettyAnn (forgetTypesPCTerm pcterm)

instance PrettyAnn RST.PrdCnsTerm where
  prettyAnn pcterm = prettyAnn (reparsePCTerm pcterm)

instance PrettyAnn CST.PrdCnsTerm where
  prettyAnn (CST.PrdTerm tm) = prettyAnn tm
  prettyAnn (CST.CnsTerm tm) = prettyAnn tm

-- Substitution

splitSubstCST :: CST.Substitution -> [NonEmpty CST.PrdCnsTerm]
splitSubstCST = NE.groupBy f
  where
    f :: CST.PrdCnsTerm -> CST.PrdCnsTerm -> Bool
    f (CST.PrdTerm _) (CST.PrdTerm _) = True
    f (CST.CnsTerm _) (CST.CnsTerm _) = True
    f _ _ = False

printSegmentCST :: NonEmpty CST.PrdCnsTerm -> Doc Annotation
printSegmentCST (CST.PrdTerm e :| rest) = parens'   comma (prettyAnn <$> CST.PrdTerm e : rest)
printSegmentCST (CST.CnsTerm e :| rest) = brackets' comma (prettyAnn <$> CST.CnsTerm e : rest)

instance {-# OVERLAPPING #-} PrettyAnn AST.Substitution where
  prettyAnn subst = prettyAnn (forgetTypesSubst subst)

instance {-# OVERLAPPING #-} PrettyAnn RST.Substitution where
  prettyAnn subst = prettyAnn (reparseSubst subst)

instance {-# OVERLAPPING #-} PrettyAnn CST.Substitution where
  prettyAnn subst = mconcat (printSegmentCST <$> splitSubstCST subst)

-- SubstitutionI

instance PrettyAnn (AST.SubstitutionI pc) where
  prettyAnn substi = prettyAnn (forgetTypesSubstI substi)

instance PrettyAnn (RST.SubstitutionI pc) where
  prettyAnn substi = prettyAnn (reparseSubstI substi)
    
instance PrettyAnn CST.SubstitutionI where
  prettyAnn (subst1, Prd, subst2) = prettyAnn subst1 <> pretty ("[*]" :: String) <> prettyAnn subst2
  prettyAnn (subst1, Cns, subst2) = prettyAnn subst1 <> pretty ("(*)" :: String) <> prettyAnn subst2

---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

instance PrettyAnn (AST.Term pc) where
  prettyAnn tm = prettyAnn (forgetTypesTerm tm)

instance PrettyAnn (RST.Term pc) where
  prettyAnn tm = prettyAnn (reparseTerm tm)

instance PrettyAnn CST.Term where
  prettyAnn (CST.Var _ v) =
    prettyAnn v
  prettyAnn (CST.Xtor _ xt args) =
    prettyAnn xt <>
    prettyAnn args
  prettyAnn (CST.XMatch _ Codata cases) =
    annKeyword "cocase" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (CST.XMatch _ Data cases) =
    annKeyword "case"   <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (CST.MuAbs _ v cmd) =
    annKeyword "mu" <+>
    prettyAnn v <>
    "." <>
    parens (prettyAnn cmd)
  prettyAnn (CST.Dtor _ xt t substi) =
      parens ( prettyAnn t <> "." <> prettyAnn xt <> prettyAnn substi )
  prettyAnn (CST.Case _ t cases) =
    annKeyword "case" <+>
    prettyAnn t <+>
    annKeyword "of" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (CST.Cocase _ cocases) =
    annKeyword "cocase" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cocases)))))
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
    (hsep (NE.toList ((\(xt,substi,_) -> annSymbol "." <> prettyAnn xt <> prettyAnn substi) <$> rst)))

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

instance PrettyAnn AST.Command where
  prettyAnn cmd = prettyAnn (forgetTypesCommand cmd)

instance PrettyAnn RST.Command where
  prettyAnn cmd = prettyAnn (reparseCommand cmd)

instance PrettyAnn CST.Command where
  prettyAnn (CST.ExitSuccess _)=
    annKeyword "ExitSuccess"
  prettyAnn (CST.ExitFailure _)=
    annKeyword "ExitFailure"
  prettyAnn (CST.Print _ t cmd) =
    annKeyword "Print" <>
    parens (prettyAnn t) <>
    semi <+>
    prettyAnn cmd
  prettyAnn (CST.Read _ cns) =
    annKeyword "Read" <>
    brackets (prettyAnn cns)
  prettyAnn (CST.Jump _ nm) = prettyAnn nm
  prettyAnn (CST.Apply _ t1 t2) =
    group (nest 3 (line' <> vsep [prettyAnn t1, annSymbol ">>", prettyAnn t2]))
  prettyAnn (CST.PrimOp _ pt op subst) =
    annKeyword (prettyAnn (primOpKeyword op)) <>
    annTypeName (prettyAnn (primTypeKeyword pt)) <>
    prettyAnn subst
  prettyAnn (CST.CommandParens _ cmd) =
    parens (prettyAnn cmd)


