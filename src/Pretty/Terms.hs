module Pretty.Terms where

import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NE
import Prettyprinter

import Pretty.Pretty
import Syntax.AST.Terms
import Syntax.CommonTerm
import Data.Bifunctor



---------------------------------------------------------------------------------
-- Pattern match cases and cocases
---------------------------------------------------------------------------------

instance PrettyAnn (CmdCase ext) where
  prettyAnn MkCmdCase{ cmdcase_name, cmdcase_args, cmdcase_cmd } =
      prettyAnn cmdcase_name <>
      printCasesArgs cmdcase_args <+>
      annSymbol "=>" <+>
      prettyAnn cmdcase_cmd

instance PrettyAnn (TermCase ext) where
  prettyAnn MkTermCase{ tmcase_name, tmcase_args, tmcase_term } =
      prettyAnn tmcase_name <>
      printCasesArgs tmcase_args <+>
      annSymbol "=>" <+>
      prettyAnn tmcase_term

instance PrettyAnn (TermCaseI ext) where
  prettyAnn MkTermCaseI { tmcasei_name, tmcasei_args = (as1, (), as2), tmcasei_term } =
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

instance PrettyAnn (PrdCnsTerm ext) where
  prettyAnn (PrdTerm tm) = prettyAnn tm
  prettyAnn (CnsTerm tm) = prettyAnn tm

splitSubst :: Substitution ext -> [NonEmpty (PrdCnsTerm ext)]
splitSubst = NE.groupBy f
  where
    f :: PrdCnsTerm ext -> PrdCnsTerm ext -> Bool
    f (PrdTerm _) (PrdTerm _) = True
    f (CnsTerm _) (CnsTerm _) = True
    f _ _ = False

printSegment :: NonEmpty (PrdCnsTerm ext) -> Doc Annotation
printSegment (PrdTerm e :| rest) = parens'   comma (prettyAnn <$> PrdTerm e : rest)
printSegment (CnsTerm e :| rest) = brackets' comma (prettyAnn <$> CnsTerm e : rest)


instance {-# OVERLAPPING #-} PrettyAnn (Substitution ext) where
  prettyAnn subst = mconcat (printSegment <$> splitSubst subst)

instance PrettyAnn (SubstitutionI ext pc) where
  prettyAnn (subst1, PrdRep, subst2) = prettyAnn subst1 <> pretty ("[*]" :: String) <> prettyAnn subst2
  prettyAnn (subst1, CnsRep, subst2) = prettyAnn subst1 <> pretty ("(*)" :: String) <> prettyAnn subst2

---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

isNumSTerm :: Term pc ext -> Maybe Int
isNumSTerm (Xtor _ PrdRep (MkXtorName Nominal "Z") []) = Just 0
isNumSTerm (Xtor _ PrdRep (MkXtorName Nominal "S") [PrdTerm n]) = case isNumSTerm n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumSTerm _ = Nothing

instance PrettyAnn (Term pc ext) where
  prettyAnn (isNumSTerm -> Just n) = pretty n
  prettyAnn (BoundVar _ _ (i,j)) = parens (pretty i <> "," <> pretty j)
  prettyAnn (FreeVar _ _ v) = pretty v
  prettyAnn (Xtor _ _ xt args) = prettyAnn xt <> prettyAnn args
  prettyAnn (XMatch _ PrdRep _ cases) =
    annKeyword "comatch" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (XMatch _ CnsRep _ cases) =
    annKeyword "match"   <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (MuAbs _ pc a cmd) =
    annKeyword (case pc of {PrdRep -> "mu"; CnsRep -> "mu"}) <+>
    prettyAnn a <> "." <> parens (prettyAnn cmd)
  prettyAnn (Dtor _ xt t substi) =
      parens ( prettyAnn t <> "." <> prettyAnn xt <> prettyAnn substi )
  prettyAnn (Case _ _ t cases) =
    annKeyword "case" <+>
    prettyAnn t <+>
    annKeyword "of" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (Cocase _ _ cocases) =
    annKeyword "cocase" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cocases)))))

instance PrettyAnn (Command ext) where
  prettyAnn (Done _)= annKeyword "Done"
  prettyAnn (Print _ t cmd) = annKeyword "Print" <> parens (prettyAnn t) <> semi <+> prettyAnn cmd
  prettyAnn (Read _ cns) = annKeyword "Read" <> brackets (prettyAnn cns)
  prettyAnn (Call _ nm) = prettyAnn nm
  prettyAnn (Apply _ _ t1 t2) = group (nest 3 (line' <> vsep [prettyAnn t1, annSymbol ">>", prettyAnn t2]))

instance PrettyAnn (NamedRep (Term pc ext)) where
  prettyAnn (NamedRep tm) = prettyAnn (openTermComplete tm)

instance PrettyAnn (NamedRep (Command ext)) where
  prettyAnn (NamedRep cmd) = prettyAnn (openCommandComplete cmd)

