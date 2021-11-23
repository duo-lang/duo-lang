module Pretty.Types where

import Prettyprinter

import Pretty.Pretty
import Syntax.Types
import Syntax.Kinds
import Syntax.CommonTerm

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

instance PrettyAnn CallingConvention  where
  prettyAnn CBV = "CBV"
  prettyAnn CBN = "CBN"

instance PrettyAnn Kind where
  prettyAnn (MonoKind eo) = "Type" <+> prettyAnn eo
  prettyAnn (KindVar var) = pretty var

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
  prettyAnn (TyData _ Nothing xtors)   = angles' pipeSym  (prettyAnn <$> xtors)
  prettyAnn (TyCodata _ Nothing xtors) = braces' commaSym (prettyAnn <$> xtors)
  -- Refinement types
  prettyAnn (TyData pr (Just tn) xtors)   = dbraces' mempty [prettyAnn tn <+> refinementSym, prettyAnn (TyData pr Nothing xtors)]
  prettyAnn (TyCodata pr (Just tn) xtors) = dbraces' mempty [prettyAnn tn <+> refinementSym, prettyAnn (TyCodata pr Nothing xtors)]

instance PrettyAnn (PrdCnsType pol) where
  prettyAnn (PrdType ty) = prettyAnn ty
  prettyAnn (CnsType ty) = prettyAnn ty

split :: LinearContext pol -> [(PrdCns, LinearContext pol)]
split [] = []
split (PrdType ty :rest) = reverse $ split' Prd rest [PrdType ty] []
split (CnsType ty :rest) = reverse $ split' Cns rest [CnsType ty] []

split' :: PrdCns -> LinearContext pol -> LinearContext pol -> [(PrdCns, LinearContext pol)] -> [(PrdCns, LinearContext pol)]
split' pc [] ctxt accum = (pc,ctxt):accum
split' Prd (PrdType ty:rest) ctxt accum = split' Prd rest (PrdType ty:ctxt) accum
split' Prd (CnsType ty:rest) ctxt accum = split' Cns rest [CnsType ty] ((Prd, reverse ctxt):accum)
split' Cns (CnsType ty:rest) ctxt accum = split' Cns rest (CnsType ty:ctxt) accum
split' Cns (PrdType ty:rest) ctxt accum = split' Prd rest [PrdType ty] ((Cns, reverse ctxt):accum)

printSegment :: (PrdCns, LinearContext pol) -> Doc Annotation
printSegment (Prd, ctxt) = parens'   comma (prettyAnn <$> ctxt)
printSegment (Cns, ctxt) = brackets' comma (prettyAnn <$> ctxt)

instance {-# OVERLAPPING #-} PrettyAnn (LinearContext pol) where
  prettyAnn ctxt = mconcat (printSegment <$> split ctxt)

instance PrettyAnn (XtorSig a) where
  prettyAnn (MkXtorSig xt args) = prettyAnn xt <> prettyAnn args

instance PrettyAnn (TypeScheme pol) where
  prettyAnn (TypeScheme [] ty) =
    prettyAnn ty
  prettyAnn (TypeScheme tvs ty) =
    forallSym <+> sep (prettyAnn <$> tvs) <> "." <+> prettyAnn ty

instance PrettyAnn TypeName where
  prettyAnn (MkTypeName tn) = annTypeName (pretty tn)

