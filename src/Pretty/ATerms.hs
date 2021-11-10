module Pretty.ATerms where

import Prettyprinter

import Pretty.Pretty
import Syntax.ATerms

---------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------


instance PrettyAnn (ACase ext) where
  prettyAnn MkACase{ acase_name, acase_args, acase_term } =
    prettyAnn acase_name <>
    parens (intercalateComma (prettyAnn <$> acase_args)) <+>
    annSymbol "=>" <+>
    prettyAnn acase_term

instance PrettyAnn (ATerm ext) where
  prettyAnn (Dtor _ xt t args) =
    parens ( prettyAnn t <> "." <> prettyAnn xt <> parens (intercalateComma (map prettyAnn args)))
  prettyAnn (Match _ t cases) =
    annKeyword "match" <+>
    prettyAnn t <+>
    annKeyword "with" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (Comatch _ cocases) =
    annKeyword "comatch" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cocases)))))

instance PrettyAnn (NamedRep (ATerm ext)) where
  prettyAnn (NamedRep tm) = prettyAnn (openATermComplete tm)
