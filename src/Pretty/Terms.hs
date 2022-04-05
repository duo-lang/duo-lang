module Pretty.Terms where

import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NE
import Prettyprinter

import Pretty.Common ()
import Pretty.Pretty
import Syntax.AST.Terms qualified as AST
import Syntax.RST.Terms qualified as RST
import Syntax.Core.Terms qualified as Core
import Syntax.Common
import Data.Bifunctor
import Translate.ForgetTypes

---------------------------------------------------------------------------------
-- Pattern match cases and cocases
---------------------------------------------------------------------------------

instance PrettyAnn AST.CmdCase where
  prettyAnn cmdcase = prettyAnn (forgetTypesCmdCase cmdcase)

instance PrettyAnn RST.CmdCase where
  prettyAnn RST.MkCmdCase{ cmdcase_name, cmdcase_args, cmdcase_cmd } =
      prettyAnn cmdcase_name <>
      printCasesArgs cmdcase_args <+>
      annSymbol "=>" <+>
      prettyAnn cmdcase_cmd

instance PrettyAnn AST.TermCase where
  prettyAnn termcase = prettyAnn (forgetTypesTermCase termcase)

instance PrettyAnn RST.TermCase where
  prettyAnn RST.MkTermCase{ tmcase_name, tmcase_args, tmcase_term } =
      prettyAnn tmcase_name <>
      printCasesArgs tmcase_args <+>
      annSymbol "=>" <+>
      prettyAnn tmcase_term

instance PrettyAnn AST.TermCaseI where
  prettyAnn termcasei = prettyAnn (forgetTypesTermCaseI termcasei)

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
  prettyAnn pcterm = prettyAnn (forgetTypesPCTerm pcterm)

instance PrettyAnn RST.PrdCnsTerm where
  prettyAnn (RST.PrdTerm tm) = prettyAnn tm
  prettyAnn (RST.CnsTerm tm) = prettyAnn tm

splitSubstRST :: RST.Substitution -> [NonEmpty RST.PrdCnsTerm]
splitSubstRST = NE.groupBy f
  where
    f :: RST.PrdCnsTerm -> RST.PrdCnsTerm -> Bool
    f (RST.PrdTerm _) (RST.PrdTerm _) = True
    f (RST.CnsTerm _) (RST.CnsTerm _) = True
    f _ _ = False
    
printSegmentRST :: NonEmpty RST.PrdCnsTerm -> Doc Annotation
printSegmentRST (RST.PrdTerm e :| rest) = parens'   comma (prettyAnn <$> RST.PrdTerm e : rest)
printSegmentRST (RST.CnsTerm e :| rest) = brackets' comma (prettyAnn <$> RST.CnsTerm e : rest)

instance {-# OVERLAPPING #-} PrettyAnn AST.Substitution where
  prettyAnn subst = prettyAnn (forgetTypesSubst subst)

instance {-# OVERLAPPING #-} PrettyAnn RST.Substitution where
  prettyAnn subst = mconcat (printSegmentRST <$> splitSubstRST subst)

instance PrettyAnn (AST.SubstitutionI pc) where
  prettyAnn substi = prettyAnn (forgetTypesSubstI substi)

instance PrettyAnn (RST.SubstitutionI pc) where
  prettyAnn (subst1, PrdRep, subst2) = prettyAnn subst1 <> pretty ("[*]" :: String) <> prettyAnn subst2
  prettyAnn (subst1, CnsRep, subst2) = prettyAnn subst1 <> pretty ("(*)" :: String) <> prettyAnn subst2
  
---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

isNumSTermRST :: RST.Term pc -> Maybe Int
isNumSTermRST (RST.Xtor _ PrdRep Nominal (MkXtorName "Z") []) = Just 0
isNumSTermRST (RST.Xtor _ PrdRep Nominal (MkXtorName "S") [RST.PrdTerm n]) = case isNumSTermRST n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumSTermRST _ = Nothing

instance PrettyAnn (Core.Term pc) where
  prettyAnn = undefined

instance PrettyAnn (AST.Term pc) where
  prettyAnn tm = prettyAnn (forgetTypesTerm tm)

instance PrettyAnn (RST.Term pc) where
  prettyAnn (isNumSTermRST -> Just n) =
    pretty n
  prettyAnn (RST.BoundVar _ _ (i,j)) =
    parens (pretty i <> "," <> pretty j)
  prettyAnn (RST.FreeVar _ _ v) =
    prettyAnn v
  prettyAnn (RST.Xtor _ _ _ xt args) =
    prettyAnn xt <> prettyAnn args
  prettyAnn (RST.XMatch _ PrdRep _ cases) =
    annKeyword "cocase" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (RST.XMatch _ CnsRep _ cases) =
    annKeyword "case"   <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (RST.MuAbs _ pc a cmd) =
    annKeyword (case pc of {PrdRep -> "mu"; CnsRep -> "mu"}) <+>
    prettyAnn a <> "." <> parens (prettyAnn cmd)
  prettyAnn (RST.Dtor _ _ _ xt t substi) =
      parens ( prettyAnn t <> "." <> prettyAnn xt <> prettyAnn substi )
  prettyAnn (RST.Case _ _ t cases) =
    annKeyword "case" <+>
    prettyAnn t <+>
    annKeyword "of" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (RST.Cocase _ _ cocases) =
    annKeyword "cocase" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cocases)))))
  prettyAnn (RST.PrimLitI64 _ i) = annLiteral (prettyAnn i <> "#I64")
  prettyAnn (RST.PrimLitF64 _ f) = annLiteral (prettyAnn f <> "#F64")

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------
instance PrettyAnn Core.Command where
  prettyAnn = undefined

instance PrettyAnn AST.Command where
  prettyAnn cmd = prettyAnn (forgetTypesCommand cmd)

instance PrettyAnn RST.Command where
  prettyAnn (RST.ExitSuccess _)= annKeyword "ExitSuccess"
  prettyAnn (RST.ExitFailure _)= annKeyword "ExitFailure"
  prettyAnn (RST.Print _ t cmd) = annKeyword "Print" <> parens (prettyAnn t) <> semi <+> prettyAnn cmd
  prettyAnn (RST.Read _ cns) = annKeyword "Read" <> brackets (prettyAnn cns)
  prettyAnn (RST.Jump _ nm) = prettyAnn nm
  prettyAnn (RST.Apply _ t1 t2) = group (nest 3 (line' <> vsep [prettyAnn t1, annSymbol ">>", prettyAnn t2]))
  prettyAnn (RST.PrimOp _ pt op subst) = annKeyword (prettyAnn (primOpKeyword op)) <> annTypeName (prettyAnn (primTypeKeyword pt)) <> prettyAnn subst

instance PrettyAnn (NamedRep (AST.Term pc)) where
  prettyAnn (NamedRep tm) = prettyAnn (NamedRep (forgetTypesTerm tm))

instance PrettyAnn (NamedRep (RST.Term pc)) where
  prettyAnn (NamedRep tm) = prettyAnn (RST.openTermComplete tm)

instance PrettyAnn (NamedRep AST.Command) where
  prettyAnn (NamedRep cmd) = prettyAnn (NamedRep (forgetTypesCommand cmd))

instance PrettyAnn (NamedRep RST.Command) where
  prettyAnn (NamedRep cmd) = prettyAnn (RST.openCommandComplete cmd)