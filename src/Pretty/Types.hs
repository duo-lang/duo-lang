module Pretty.Types where

import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NE
import Prettyprinter

import Pretty.Common ()
import Pretty.Pretty
import Syntax.RST.Types
import Syntax.Common
import Control.Applicative (Alternative(empty))

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

instance PrettyAnn (VariantType pol) where
  prettyAnn (CovariantType ty) = prettyAnn ty
  prettyAnn (ContravariantType ty) = prettyAnn ty

resugarType :: Typ pol -> Maybe (Doc Annotation, BinOp, Doc Annotation)
resugarType (TyNominal _ _ _ (MkTypeName "Fun") [ContravariantType tl, CovariantType tr]) =
  Just (prettyAnn tl , CustomOp (MkTyOpName "->"), prettyAnn tr)
resugarType (TyNominal _ _ _ (MkTypeName "Par") [CovariantType t1, CovariantType t2]) =
  Just (prettyAnn t1 , CustomOp (MkTyOpName "⅋"), prettyAnn t2)
resugarType _ = Nothing

instance PrettyAnn (Typ pol) where
  -- Sugared types
  prettyAnn (resugarType -> Just (ty1, binOp, ty2)) = parens (ty1 <+> prettyAnn binOp <+> ty2)
  -- Lattice types
  prettyAnn (TySet _ PosRep _ [])  = botSym
  prettyAnn (TySet _ PosRep _ [t]) = prettyAnn t
  prettyAnn (TySet _ PosRep _ tts) = parens' unionSym (map prettyAnn tts)
  prettyAnn (TySet _ NegRep _ [])  = topSym
  prettyAnn (TySet _ NegRep _ [t]) = prettyAnn t
  prettyAnn (TySet _ NegRep _ tts) = parens' interSym (map prettyAnn tts)
  -- Type Variables
  prettyAnn (TyVar _ _ _ tv)       = prettyAnn tv
  -- Recursive types
  prettyAnn (TyRec _ _ rv t)       = recSym <+> prettyAnn rv <> "." <> align (prettyAnn t)
  -- Nominal types
  prettyAnn (TyNominal _ _ _ tn args) = prettyAnn tn <> parens' commaSym (prettyAnn <$> args)
  -- Structural data and codata types
  prettyAnn (TyData _ _ Nothing xtors)   = angles' commaSym  (prettyAnn <$> xtors)
  prettyAnn (TyCodata _ _ Nothing xtors) = braces' commaSym (prettyAnn <$> xtors)
  -- Refinement types
  prettyAnn (TyData _ _ (Just tn) xtors)   = angles' mempty [prettyAnn tn <+> pipeSym, hsep (intersperse commaSym (prettyAnn <$> xtors))]
  prettyAnn (TyCodata _ _ (Just tn) xtors) = braces' mempty [prettyAnn tn <+> pipeSym, hsep (intersperse commaSym (prettyAnn <$> xtors))]
  prettyAnn (TyPrim _ _ pt) = "#" <> prettyAnn pt

instance PrettyAnn (PrdCnsType pol) where
  prettyAnn (PrdCnsType PrdRep ty) = prettyAnn ty
  prettyAnn (PrdCnsType CnsRep ty) = "return " <> prettyAnn ty

splitCtxt :: LinearContext pol -> [NonEmpty (PrdCnsType pol)]
splitCtxt = NE.groupBy f
  where
    f :: PrdCnsType pol -> PrdCnsType pol -> Bool
    f (PrdCnsType PrdRep _) (PrdCnsType PrdRep _) = True
    f (PrdCnsType CnsRep _) (PrdCnsType CnsRep _) = True
    f (PrdCnsType _ _) (PrdCnsType _ _) = False

printSegment :: LinearContext pol -> Doc Annotation
printSegment xs = parens'   comma (prettyAnn <$> xs)

instance {-# OVERLAPPING #-} PrettyAnn (LinearContext pol) where
  prettyAnn ctxt = printSegment ctxt

instance PrettyAnn (XtorSig a) where
  prettyAnn (MkXtorSig xt args) = prettyAnn xt <> prettyAnn args

instance PrettyAnn (TypeScheme pol) where
  prettyAnn (TypeScheme { ts_vars = [], ts_monotype }) =
    prettyAnn ts_monotype
  prettyAnn (TypeScheme { ts_vars, ts_monotype }) =
    forallSym <+>
    sep (prettyAnn <$> ts_vars ) <>
    "." <+>
    prettyAnn ts_monotype
