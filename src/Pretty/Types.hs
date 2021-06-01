{-# LANGUAGE OverloadedStrings #-}
module Pretty.Types where

import Prettyprinter

import Pretty.Pretty
import Syntax.Types

---------------------------------------------------------------------------------
-- Prettyprinting of Types
---------------------------------------------------------------------------------

instance PrettyAnn TVar where
  prettyAnn (MkTVar tv) = pretty tv

instance PrettyAnn (Typ pol) where
  prettyAnn (TySet PosRep []) = annKeyword "Bot"
  prettyAnn (TySet PosRep [t]) = prettyAnn t
  prettyAnn (TySet PosRep tts) = parens (intercalateX " \\/ " (map prettyAnn tts))
  prettyAnn (TySet NegRep []) = annKeyword "Top"
  prettyAnn (TySet NegRep [t]) = prettyAnn t
  prettyAnn (TySet NegRep tts) = parens (intercalateX " /\\ " (map prettyAnn tts))
  prettyAnn (TyVar _ tv) = prettyAnn tv
  prettyAnn (TyRec _ rv t) = annKeyword "rec " <> prettyAnn rv <> "." <> prettyAnn t
  prettyAnn (TyNominal _ tn) = prettyAnn tn
  prettyAnn (TyRefined _ tn t) = 
    dbraces ( mempty <+> prettyAnn t <+> "<<:" <+> prettyAnn tn <+> mempty )
  prettyAnn (TyData _ xtors) =
    angles (mempty <+> cat (punctuate " | " (prettyAnn <$> xtors)) <+> mempty)
  prettyAnn (TyCodata _ xtors) =
    braces (mempty <+> cat (punctuate " , " (prettyAnn <$> xtors)) <+> mempty)

instance PrettyAnn (TypArgs a) where
  prettyAnn (MkTypArgs prdArgs cnsArgs) = prettyTwice' prdArgs cnsArgs

instance PrettyAnn (XtorSig a) where
  prettyAnn (MkXtorSig xt args) = prettyAnn xt <> prettyAnn args

instance PrettyAnn (TypeScheme pol) where
  prettyAnn (TypeScheme [] ty) = prettyAnn ty
  prettyAnn (TypeScheme tvs ty) =
    annKeyword "forall" <+>
    intercalateX " " (map prettyAnn tvs) <>
    "." <+>
    prettyAnn ty

instance PrettyAnn TypeName where
  prettyAnn (MkTypeName tn) = annTypeName (pretty tn)

