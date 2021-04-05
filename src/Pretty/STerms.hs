{-# LANGUAGE OverloadedStrings #-}
module Pretty.STerms where

import Prettyprinter

import Pretty.Pretty
import Syntax.STerms

---------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------

instance PrettyAnn a => PrettyAnn (SCase a) where
  prettyAnn MkSCase{..} =
    prettyAnn scase_name <>
    prettyTwice scase_args <+>
    annSymbol "=>" <+>
    prettyAnn scase_cmd

instance PrettyAnn a => PrettyAnn (XtorArgs a) where
  prettyAnn (MkXtorArgs prds cns) = prettyTwice' prds cns

isNumSTerm :: STerm pc a -> Maybe Int
isNumSTerm (XtorCall PrdRep (MkXtorName Nominal "Z") (MkXtorArgs [] [])) = Just 0
isNumSTerm (XtorCall PrdRep (MkXtorName Nominal "S") (MkXtorArgs [n] [])) = case isNumSTerm n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumSTerm _ = Nothing

instance PrettyAnn a => PrettyAnn (STerm pc a) where
  prettyAnn (isNumSTerm -> Just n) = pretty n
  prettyAnn (BoundVar _ (i,j)) = parens (pretty i <> "," <> pretty j)
  prettyAnn (FreeVar _ v) = pretty v
  prettyAnn (XtorCall _ xt args) = prettyAnn xt <> prettyAnn args
  prettyAnn (XMatch PrdRep _ cases) =
    annKeyword "comatch" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (XMatch CnsRep _ cases) =
    annKeyword "match"   <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (MuAbs pc a cmd) =
    annKeyword (case pc of {PrdRep -> "mu"; CnsRep -> "mu*"}) <+>
    prettyAnn a <> "." <> parens (prettyAnn cmd)

instance PrettyAnn a => PrettyAnn (Command a) where
  prettyAnn Done = annKeyword "Done"
  prettyAnn (Print t) = annKeyword "Print" <> parens (prettyAnn t)
  prettyAnn (Apply t1 t2) = group (nest 3 (line' <> vsep [prettyAnn t1, annSymbol ">>", prettyAnn t2]))

instance PrettyAnn (NamedRep (STerm pc FreeVarName)) where
  prettyAnn (NamedRep tm) = prettyAnn (openSTermComplete tm)

instance PrettyAnn (NamedRep (Command FreeVarName)) where
  prettyAnn (NamedRep cmd) = prettyAnn (openCommandComplete cmd)

