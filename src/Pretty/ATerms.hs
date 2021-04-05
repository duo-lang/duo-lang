{-# LANGUAGE OverloadedStrings #-}
module Pretty.ATerms where

import Prettyprinter

import Pretty.Pretty
import Syntax.ATerms

---------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------

isNumATerm :: ATerm ext a -> Maybe Int
isNumATerm (Ctor _ (MkXtorName Nominal "Z") []) = Just 0
isNumATerm (Ctor _ (MkXtorName Nominal "S") [n]) = case isNumATerm n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumATerm _ = Nothing

instance PrettyAnn a => PrettyAnn (ACase ext a) where
  prettyAnn MkACase{ acase_name, acase_args, acase_term } =
    prettyAnn acase_name <>
    parens (intercalateComma (prettyAnn <$> acase_args)) <+>
    annSymbol "=>" <+>
    prettyAnn acase_term

instance PrettyAnn a => PrettyAnn (ATerm ext a) where
  prettyAnn (isNumATerm -> Just n) = pretty n
  prettyAnn (BVar _ (i,j)) = parens (pretty i <> "," <> pretty j)
  prettyAnn (FVar _ v) = pretty v
  prettyAnn (Ctor _ xt args) = prettyAnn xt <> parens (intercalateComma (map prettyAnn args))
  prettyAnn (Dtor _ xt t args) =
    parens ( prettyAnn t <> "." <> prettyAnn xt <> parens (intercalateComma (map prettyAnn args)))
  prettyAnn (Match t cases) =
    annKeyword "match" <+>
    prettyAnn t <+>
    annKeyword "with" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (Comatch cocases) =
    annKeyword "comatch" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cocases)))))

instance PrettyAnn (NamedRep (ATerm () FreeVarName)) where
  prettyAnn (NamedRep tm) = prettyAnn (openATermComplete tm)
