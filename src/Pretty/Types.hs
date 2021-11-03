module Pretty.Types where

import Prettyprinter

import Pretty.Pretty
import Syntax.Types
import Syntax.Kinds

---------------------------------------------------------------------------------
-- Symbols used in the prettyprinting of types
---------------------------------------------------------------------------------

botSym :: Doc Annotation
botSym = annKeyword "Bot"

topSym :: Doc Annotation
topSym = annKeyword "Top"

unionSym :: Doc Annotation
unionSym = annKeyword "\\/"

interSym :: Doc Annotation
interSym = annKeyword "/\\"

recSym :: Doc Annotation
recSym = annKeyword "rec"

refinementSym :: Doc Annotation
refinementSym = annKeyword ":>>"

forallSym :: Doc Annotation
forallSym = annKeyword "forall"

pipeSym :: Doc Annotation
pipeSym = prettyAnn ("|" :: String)

commaSym :: Doc Annotation
commaSym = prettyAnn ("," :: String)


---------------------------------------------------------------------------------
-- Prettyprinting of Kinds
---------------------------------------------------------------------------------

instance PrettyAnn KVar where
  prettyAnn kv = pretty (unKVar kv)

instance PrettyAnn CallingConvention  where
  prettyAnn CBV = "CBV"
  prettyAnn CBN = "CBN"

instance PrettyAnn Kind where
  prettyAnn (MonoKind eo) = "Type" <+> prettyAnn eo
  prettyAnn (KindVar var) = prettyAnn var

---------------------------------------------------------------------------------
-- Prettyprinting of types
---------------------------------------------------------------------------------

instance PrettyAnn Polarity where
  prettyAnn Pos = "Pos"
  prettyAnn Neg = "Neg"

instance PrettyAnn TVar where
  prettyAnn (MkTVar tv) = pretty tv

instance PrettyAnn (Typ pol) where
  -- Lattice types
  prettyAnn (TySet PosRep _ [])  = botSym
  prettyAnn (TySet PosRep _ [t]) = prettyAnn t
  prettyAnn (TySet PosRep _ tts) = parens' unionSym (map prettyAnn tts)
  prettyAnn (TySet NegRep _ [])  = topSym
  prettyAnn (TySet NegRep _ [t]) = prettyAnn t
  prettyAnn (TySet NegRep _ tts) = parens' interSym (map prettyAnn tts)
  -- Type Variables
  prettyAnn (TyVar _ _ tv)       = prettyAnn tv
  -- Recursive types
  prettyAnn (TyRec _ rv t)     = recSym <+> prettyAnn rv <> "." <> align (prettyAnn t)
  -- Nominal types
  prettyAnn (TyNominal _ tn)   = prettyAnn tn
  -- Structural data and codata types
  prettyAnn (TyData _ Nothing xtors)   = angles' pipeSym  (prettyAnn <$> xtors)
  prettyAnn (TyCodata _ Nothing xtors) = braces' commaSym (prettyAnn <$> xtors)
  -- Refinement types
  prettyAnn (TyData pr (Just tn) xtors)   = dbraces' mempty [prettyAnn tn <+> refinementSym, prettyAnn (TyData pr Nothing xtors)]
  prettyAnn (TyCodata pr (Just tn) xtors) = dbraces' mempty [prettyAnn tn <+> refinementSym, prettyAnn (TyCodata pr Nothing xtors)]

instance PrettyAnn (TypArgs a) where
  prettyAnn (MkTypArgs [] []) = mempty
  prettyAnn (MkTypArgs prdArgs []) = parens'   commaSym (prettyAnn <$> prdArgs)
  prettyAnn (MkTypArgs [] cnsArgs) = brackets' commaSym (prettyAnn <$> cnsArgs)
  prettyAnn (MkTypArgs prdArgs cnsArgs) = align $ sep [ (parens'   commaSym (prettyAnn <$> prdArgs))
                                                      , (brackets' commaSym (prettyAnn <$> cnsArgs))
                                                      ]

instance PrettyAnn (XtorSig a) where
  prettyAnn (MkXtorSig xt args) = prettyAnn xt <> prettyAnn args

instance PrettyAnn (TypeScheme pol) where
  prettyAnn (TypeScheme [] ty) =
    prettyAnn ty
  prettyAnn (TypeScheme tvs ty) =
    forallSym <+> sep (prettyAnn <$> tvs) <> "." <+> prettyAnn ty

instance PrettyAnn TypeName where
  prettyAnn (MkTypeName tn) = annTypeName (pretty tn)

