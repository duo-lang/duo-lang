module Pretty.Types where

import Prettyprinter

import Pretty.Pretty
import Syntax.Types

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
-- Prettyprinting of types
---------------------------------------------------------------------------------

instance PrettyAnn Polarity where
  prettyAnn Pos = "Pos"
  prettyAnn Neg = "Neg"

instance PrettyAnn TVar where
  prettyAnn (MkTVar tv) = pretty tv

instance PrettyAnn (Typ pol) where
  -- Lattice types
  prettyAnn (TySet PosRep [])  = botSym
  prettyAnn (TySet PosRep [t]) = prettyAnn t
  prettyAnn (TySet PosRep tts) = parens' unionSym (map prettyAnn tts)
  prettyAnn (TySet NegRep [])  = topSym
  prettyAnn (TySet NegRep [t]) = prettyAnn t
  prettyAnn (TySet NegRep tts) = parens' interSym (map prettyAnn tts)
  -- Type Variables
  prettyAnn (TyVar _ tv)       = prettyAnn tv
  -- Recursive types
  prettyAnn (TyRec _ rv t)     = recSym <+> prettyAnn rv <> "." <> align (prettyAnn t)
  -- Nominal types
  prettyAnn (TyNominal _ tn)   = prettyAnn tn
  -- Structural data and codata types
  prettyAnn (TyData _ xtors)   = angles' pipeSym  (prettyAnn <$> xtors)
  prettyAnn (TyCodata _ xtors) = braces' commaSym (prettyAnn <$> xtors)

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

