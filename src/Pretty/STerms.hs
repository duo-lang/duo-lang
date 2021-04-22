{-# LANGUAGE OverloadedStrings #-}
module Pretty.STerms where

import Prettyprinter

import Pretty.Pretty
import Syntax.STerms

---------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------

instance PrettyAnn bs => PrettyAnn (SCase ext bs) where
  prettyAnn MkSCase{..} =
    prettyAnn scase_name <>
    prettyTwice scase_args <+>
    annSymbol "=>" <+>
    prettyAnn scase_cmd

instance PrettyAnn bs => PrettyAnn (XtorArgs ext bs) where
  prettyAnn (MkXtorArgs prds cns) = prettyTwice' prds cns

isNumSTerm :: STerm pc ext a -> Maybe Int
isNumSTerm (XtorCall _ PrdRep (MkXtorName Nominal "Z") (MkXtorArgs [] [])) = Just 0
isNumSTerm (XtorCall _ PrdRep (MkXtorName Nominal "S") (MkXtorArgs [n] [])) = case isNumSTerm n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumSTerm _ = Nothing

instance PrettyAnn bs => PrettyAnn (STerm pc ext bs) where
  prettyAnn (isNumSTerm -> Just n) = pretty n
  prettyAnn (BoundVar _ _ (i,j)) = parens (pretty i <> "," <> pretty j)
  prettyAnn (FreeVar _ _ v) = pretty v
  prettyAnn (XtorCall _ _ xt args) = prettyAnn xt <> prettyAnn args
  prettyAnn (XMatch _ PrdRep _ cases) =
    annKeyword "comatch" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (XMatch _ CnsRep _ cases) =
    annKeyword "match"   <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (MuAbs _ pc a cmd) =
    annKeyword (case pc of {PrdRep -> "mu"; CnsRep -> "mu"}) <+>
    prettyAnn a <> "." <> parens (prettyAnn cmd)

instance PrettyAnn bs => PrettyAnn (Command ext bs) where
  prettyAnn (Done _)= annKeyword "Done"
  prettyAnn (Print _ t) = annKeyword "Print" <> parens (prettyAnn t)
  prettyAnn (Apply _ t1 t2) = group (nest 3 (line' <> vsep [prettyAnn t1, annSymbol ">>", prettyAnn t2]))

instance PrettyAnn (NamedRep (STerm pc ext FreeVarName)) where
  prettyAnn (NamedRep tm) = prettyAnn (openSTermComplete tm)

instance PrettyAnn (NamedRep (Command ext FreeVarName)) where
  prettyAnn (NamedRep cmd) = prettyAnn (openCommandComplete cmd)

