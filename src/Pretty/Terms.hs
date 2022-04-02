module Pretty.Terms where

import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NE
import Prettyprinter

import Pretty.Common ()
import Pretty.Pretty
import Syntax.AST.Terms qualified as AST
import Syntax.RST.Terms qualified as RST
import Syntax.Common
import Data.Bifunctor

---------------------------------------------------------------------------------
-- Pattern match cases and cocases
---------------------------------------------------------------------------------

instance PrettyAnn AST.CmdCase where
  prettyAnn AST.MkCmdCase{ cmdcase_name, cmdcase_args, cmdcase_cmd } =
      prettyAnn cmdcase_name <>
      printCasesArgs cmdcase_args <+>
      annSymbol "=>" <+>
      prettyAnn cmdcase_cmd

instance PrettyAnn RST.CmdCase where
  prettyAnn RST.MkCmdCase{ cmdcase_name, cmdcase_args, cmdcase_cmd } =
      prettyAnn cmdcase_name <>
      printCasesArgs cmdcase_args <+>
      annSymbol "=>" <+>
      prettyAnn cmdcase_cmd

instance PrettyAnn AST.TermCase where
  prettyAnn AST.MkTermCase{ tmcase_name, tmcase_args, tmcase_term } =
      prettyAnn tmcase_name <>
      printCasesArgs tmcase_args <+>
      annSymbol "=>" <+>
      prettyAnn tmcase_term

instance PrettyAnn RST.TermCase where
  prettyAnn RST.MkTermCase{ tmcase_name, tmcase_args, tmcase_term } =
      prettyAnn tmcase_name <>
      printCasesArgs tmcase_args <+>
      annSymbol "=>" <+>
      prettyAnn tmcase_term

instance PrettyAnn AST.TermCaseI where
  prettyAnn AST.MkTermCaseI { tmcasei_name, tmcasei_args = (as1, (), as2), tmcasei_term } =
    prettyAnn tmcasei_name <>
    printCasesArgs as1 <>
    pretty ("[*]" :: String) <>
    printCasesArgs as2 <+>
    annSymbol "=>" <+>
    prettyAnn tmcasei_term

instance PrettyAnn RST.TermCaseI where
  prettyAnn RST.MkTermCaseI { tmcasei_name, tmcasei_args = (as1, (), as2), tmcasei_term } =
    prettyAnn tmcasei_name <>
    printCasesArgs as1 <>
    pretty ("[*]" :: String) <>
    printCasesArgs as2 <+>
    annSymbol "=>" <+>
    prettyAnn tmcasei_term

printCasesArgs :: [(PrdCns, Maybe FreeVarName)] -> Doc Annotation
printCasesArgs cs = printCasesArgs' (second (map snd) <$> splitOnChange fst cs)

printCasesArgs' :: [(PrdCns, [Maybe FreeVarName])] -> Doc Annotation
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

instance PrettyAnn AST.PrdCnsTerm where
  prettyAnn (AST.PrdTerm tm) = prettyAnn tm
  prettyAnn (AST.CnsTerm tm) = prettyAnn tm

instance PrettyAnn RST.PrdCnsTerm where
  prettyAnn (RST.PrdTerm tm) = prettyAnn tm
  prettyAnn (RST.CnsTerm tm) = prettyAnn tm

splitSubstAST :: AST.Substitution -> [NonEmpty AST.PrdCnsTerm]
splitSubstAST = NE.groupBy f
  where
    f :: AST.PrdCnsTerm -> AST.PrdCnsTerm -> Bool
    f (AST.PrdTerm _) (AST.PrdTerm _) = True
    f (AST.CnsTerm _) (AST.CnsTerm _) = True
    f _ _ = False

splitSubstRST :: RST.Substitution -> [NonEmpty RST.PrdCnsTerm]
splitSubstRST = NE.groupBy f
  where
    f :: RST.PrdCnsTerm -> RST.PrdCnsTerm -> Bool
    f (RST.PrdTerm _) (RST.PrdTerm _) = True
    f (RST.CnsTerm _) (RST.CnsTerm _) = True
    f _ _ = False
    
printSegmentAST :: NonEmpty AST.PrdCnsTerm -> Doc Annotation
printSegmentAST (AST.PrdTerm e :| rest) = parens'   comma (prettyAnn <$> AST.PrdTerm e : rest)
printSegmentAST (AST.CnsTerm e :| rest) = brackets' comma (prettyAnn <$> AST.CnsTerm e : rest)

printSegmentRST :: NonEmpty RST.PrdCnsTerm -> Doc Annotation
printSegmentRST (RST.PrdTerm e :| rest) = parens'   comma (prettyAnn <$> RST.PrdTerm e : rest)
printSegmentRST (RST.CnsTerm e :| rest) = brackets' comma (prettyAnn <$> RST.CnsTerm e : rest)

instance {-# OVERLAPPING #-} PrettyAnn AST.Substitution where
  prettyAnn subst = mconcat (printSegmentAST <$> splitSubstAST subst)

instance {-# OVERLAPPING #-} PrettyAnn RST.Substitution where
  prettyAnn subst = mconcat (printSegmentRST <$> splitSubstRST subst)

instance PrettyAnn (AST.SubstitutionI pc) where
  prettyAnn (subst1, PrdRep, subst2) = prettyAnn subst1 <> pretty ("[*]" :: String) <> prettyAnn subst2
  prettyAnn (subst1, CnsRep, subst2) = prettyAnn subst1 <> pretty ("(*)" :: String) <> prettyAnn subst2

instance PrettyAnn (RST.SubstitutionI pc) where
  prettyAnn (subst1, PrdRep, subst2) = prettyAnn subst1 <> pretty ("[*]" :: String) <> prettyAnn subst2
  prettyAnn (subst1, CnsRep, subst2) = prettyAnn subst1 <> pretty ("(*)" :: String) <> prettyAnn subst2
  
---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

isNumSTermAST :: AST.Term pc -> Maybe Int
isNumSTermAST (AST.Xtor _ PrdRep _ Nominal (MkXtorName "Z") []) = Just 0
isNumSTermAST (AST.Xtor _ PrdRep _ Nominal (MkXtorName "S") [AST.PrdTerm n]) = case isNumSTermAST n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumSTermAST _ = Nothing

isNumSTermRST :: RST.Term pc -> Maybe Int
isNumSTermRST (RST.Xtor _ PrdRep _ Nominal (MkXtorName "Z") []) = Just 0
isNumSTermRST (RST.Xtor _ PrdRep _ Nominal (MkXtorName "S") [RST.PrdTerm n]) = case isNumSTermRST n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumSTermRST _ = Nothing

instance PrettyAnn (AST.Term pc) where
  prettyAnn (isNumSTermAST -> Just n) =
    pretty n
  prettyAnn (AST.BoundVar _ _ _ (i,j)) =
    parens (pretty i <> "," <> pretty j)
  prettyAnn (AST.FreeVar _ _ _ v) =
    prettyAnn v
  prettyAnn (AST.Xtor _ _ _ _ xt args) =
    prettyAnn xt <> prettyAnn args
  prettyAnn (AST.XMatch _ PrdRep _ _ cases) =
    annKeyword "cocase" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (AST.XMatch _ CnsRep _ _ cases) =
    annKeyword "case"   <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (AST.MuAbs _ pc _ a cmd) =
    annKeyword (case pc of {PrdRep -> "mu"; CnsRep -> "mu"}) <+>
    prettyAnn a <> "." <> parens (prettyAnn cmd)
  prettyAnn (AST.Dtor _ _ _ _ xt t substi) =
      parens ( prettyAnn t <> "." <> prettyAnn xt <> prettyAnn substi )
  prettyAnn (AST.Case _ _ _ t cases) =
    annKeyword "case" <+>
    prettyAnn t <+>
    annKeyword "of" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (AST.Cocase _ _ _ cocases) =
    annKeyword "cocase" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cocases)))))
  prettyAnn (AST.PrimLitI64 _ i) = annLiteral (prettyAnn i <> "#I64")
  prettyAnn (AST.PrimLitF64 _ f) = annLiteral (prettyAnn f <> "#F64")

instance PrettyAnn (RST.Term pc) where
  prettyAnn (isNumSTermRST -> Just n) =
    pretty n
  prettyAnn (RST.BoundVar _ _ _ (i,j)) =
    parens (pretty i <> "," <> pretty j)
  prettyAnn (RST.FreeVar _ _ _ v) =
    prettyAnn v
  prettyAnn (RST.Xtor _ _ _ _ xt args) =
    prettyAnn xt <> prettyAnn args
  prettyAnn (RST.XMatch _ PrdRep _ _ cases) =
    annKeyword "cocase" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (RST.XMatch _ CnsRep _ _ cases) =
    annKeyword "case"   <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (RST.MuAbs _ pc _ a cmd) =
    annKeyword (case pc of {PrdRep -> "mu"; CnsRep -> "mu"}) <+>
    prettyAnn a <> "." <> parens (prettyAnn cmd)
  prettyAnn (RST.Dtor _ _ _ _ xt t substi) =
      parens ( prettyAnn t <> "." <> prettyAnn xt <> prettyAnn substi )
  prettyAnn (RST.Case _ _ _ t cases) =
    annKeyword "case" <+>
    prettyAnn t <+>
    annKeyword "of" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (RST.Cocase _ _ _ cocases) =
    annKeyword "cocase" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cocases)))))
  prettyAnn (RST.PrimLitI64 _ i) = annLiteral (prettyAnn i <> "#I64")
  prettyAnn (RST.PrimLitF64 _ f) = annLiteral (prettyAnn f <> "#F64")

instance PrettyAnn AST.Command where
  prettyAnn (AST.ExitSuccess _)= annKeyword "ExitSuccess"
  prettyAnn (AST.ExitFailure _)= annKeyword "ExitFailure"
  prettyAnn (AST.Print _ t cmd) = annKeyword "Print" <> parens (prettyAnn t) <> semi <+> prettyAnn cmd
  prettyAnn (AST.Read _ cns) = annKeyword "Read" <> brackets (prettyAnn cns)
  prettyAnn (AST.Jump _ nm) = prettyAnn nm
  prettyAnn (AST.Apply _ _ t1 t2) = group (nest 3 (line' <> vsep [prettyAnn t1, annSymbol ">>", prettyAnn t2]))
  prettyAnn (AST.PrimOp _ pt op subst) = annKeyword (prettyAnn (primOpKeyword op)) <> annTypeName (prettyAnn (primTypeKeyword pt)) <> prettyAnn subst

instance PrettyAnn RST.Command where
  prettyAnn (RST.ExitSuccess _)= annKeyword "ExitSuccess"
  prettyAnn (RST.ExitFailure _)= annKeyword "ExitFailure"
  prettyAnn (RST.Print _ t cmd) = annKeyword "Print" <> parens (prettyAnn t) <> semi <+> prettyAnn cmd
  prettyAnn (RST.Read _ cns) = annKeyword "Read" <> brackets (prettyAnn cns)
  prettyAnn (RST.Jump _ nm) = prettyAnn nm
  prettyAnn (RST.Apply _ _ t1 t2) = group (nest 3 (line' <> vsep [prettyAnn t1, annSymbol ">>", prettyAnn t2]))
  prettyAnn (RST.PrimOp _ pt op subst) = annKeyword (prettyAnn (primOpKeyword op)) <> annTypeName (prettyAnn (primTypeKeyword pt)) <> prettyAnn subst

instance PrettyAnn (NamedRep (AST.Term pc)) where
  prettyAnn (NamedRep tm) = prettyAnn (AST.openTermComplete tm)

instance PrettyAnn (NamedRep (RST.Term pc)) where
  prettyAnn (NamedRep tm) = prettyAnn (RST.openTermComplete tm)

instance PrettyAnn (NamedRep AST.Command) where
  prettyAnn (NamedRep cmd) = prettyAnn (AST.openCommandComplete cmd)

instance PrettyAnn (NamedRep RST.Command) where
  prettyAnn (NamedRep cmd) = prettyAnn (RST.openCommandComplete cmd)