module Pretty.Types where

import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NE
import Prettyprinter

import Pretty.Common ()
import Pretty.Pretty
import Syntax.RST.Types qualified as RST
import Syntax.Common

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

forallSym :: Doc Annotation
forallSym = annKeyword "forall"

pipeSym :: Doc Annotation
pipeSym = prettyAnn ("|" :: String)

commaSym :: Doc Annotation
commaSym = prettyAnn ("," :: String)

arrowSym :: Doc Annotation
arrowSym = annKeyword "->"

parSym :: Doc Annotation
parSym = annKeyword "⅋"

---------------------------------------------------------------------------------
-- Prettyprinting of types
---------------------------------------------------------------------------------

instance PrettyAnn TyOpName where
  prettyAnn (MkTyOpName op) = prettyAnn op

instance PrettyAnn BinOp where
  prettyAnn (CustomOp op) = prettyAnn op
  prettyAnn UnionOp = unionSym
  prettyAnn InterOp = interSym

instance PrettyAnn (RST.VariantType pol) where
  prettyAnn (RST.CovariantType ty) = prettyAnn ty
  prettyAnn (RST.ContravariantType ty) = prettyAnn ty

resugarType :: RST.Typ pol -> Maybe (Doc Annotation, BinOp, Doc Annotation)
resugarType (RST.TyNominal _ _ _ MkRnTypeName { rnTnName = MkTypeName "Fun" } [RST.ContravariantType tl, RST.CovariantType tr]) =
  Just (prettyAnn tl , CustomOp (MkTyOpName "->"), prettyAnn tr)
resugarType (RST.TyNominal _ _ _ MkRnTypeName { rnTnName = MkTypeName "Par" } [RST.CovariantType t1, RST.CovariantType t2]) =
  Just (prettyAnn t1 , CustomOp (MkTyOpName "⅋"), prettyAnn t2)
resugarType _ = Nothing

instance PrettyAnn (RST.Typ pol) where
  -- Sugared types
  prettyAnn (resugarType -> Just (ty1, binOp, ty2)) = parens (ty1 <+> prettyAnn binOp <+> ty2)
  -- Lattice types
  prettyAnn (RST.TySet _ PosRep _ [])  = botSym
  prettyAnn (RST.TySet _ PosRep _ [t]) = prettyAnn t
  prettyAnn (RST.TySet _ PosRep _ tts) = parens' unionSym (map prettyAnn tts)
  prettyAnn (RST.TySet _ NegRep _ [])  = topSym
  prettyAnn (RST.TySet _ NegRep _ [t]) = prettyAnn t
  prettyAnn (RST.TySet _ NegRep _ tts) = parens' interSym (map prettyAnn tts)
  -- Type Variables
  prettyAnn (RST.TyVar _ _ _ tv)       = prettyAnn tv
  -- Recursive types
  prettyAnn (RST.TyRec _ _ rv t)       = recSym <+> prettyAnn rv <> "." <> align (prettyAnn t)
  -- Nominal types
  prettyAnn (RST.TyNominal _ _ _ tn args) = prettyAnn tn <> parens' commaSym (prettyAnn <$> args)
  prettyAnn (RST.TySyn _ _ nm _) = prettyAnn nm
  -- Structural data and codata types
  prettyAnn (RST.TyData _ _ Nothing xtors)   = angles' commaSym  (prettyAnn <$> xtors)
  prettyAnn (RST.TyCodata _ _ Nothing xtors) = braces' commaSym (prettyAnn <$> xtors)
  -- Refinement types
  prettyAnn (RST.TyData _ _ (Just tn) xtors)   = angles' mempty [prettyAnn tn <+> pipeSym, hsep (intersperse commaSym (prettyAnn <$> xtors))]
  prettyAnn (RST.TyCodata _ _ (Just tn) xtors) = braces' mempty [prettyAnn tn <+> pipeSym, hsep (intersperse commaSym (prettyAnn <$> xtors))]
  prettyAnn (RST.TyPrim _ _ pt) = "#" <> prettyAnn pt

instance PrettyAnn (RST.PrdCnsType pol) where
  prettyAnn (RST.PrdCnsType _ ty) = prettyAnn ty

splitCtxt :: RST.LinearContext pol -> [NonEmpty (RST.PrdCnsType pol)]
splitCtxt = NE.groupBy f
  where
    f :: RST.PrdCnsType pol -> RST.PrdCnsType pol -> Bool
    f (RST.PrdCnsType PrdRep _) (RST.PrdCnsType PrdRep _) = True
    f (RST.PrdCnsType CnsRep _) (RST.PrdCnsType CnsRep _) = True
    f (RST.PrdCnsType _ _) (RST.PrdCnsType _ _) = False

printSegment :: NonEmpty (RST.PrdCnsType pol) -> Doc Annotation
printSegment (RST.PrdCnsType PrdRep ty :| rest) = parens'   comma (prettyAnn <$> RST.PrdCnsType PrdRep ty : rest)
printSegment (RST.PrdCnsType CnsRep ty :| rest) = brackets' comma (prettyAnn <$> RST.PrdCnsType CnsRep ty : rest)

instance {-# OVERLAPPING #-} PrettyAnn (RST.LinearContext pol) where
  prettyAnn ctxt = mconcat (printSegment <$> splitCtxt ctxt)

instance PrettyAnn (RST.XtorSig a) where
  prettyAnn (RST.MkXtorSig xt args) = prettyAnn xt <> prettyAnn args

instance PrettyAnn (RST.TypeScheme pol) where
  prettyAnn (RST.TypeScheme { ts_vars = [], ts_monotype }) =
    prettyAnn ts_monotype
  prettyAnn (RST.TypeScheme { ts_vars, ts_monotype }) =
    forallSym <+>
    sep (prettyAnn <$> ts_vars ) <>
    "." <+>
    prettyAnn ts_monotype
