module Pretty.Types where

import Data.List (intersperse)
import Data.List.NonEmpty qualified as NE
import Prettyprinter

import Pretty.Common ()
import Pretty.Pretty
import Syntax.Common.TypesPol qualified as RST
import Syntax.Common.TypesUnpol qualified as CST
import Translate.Reparse
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

returnKw :: Doc Annotation
returnKw = annKeyword "return"

---------------------------------------------------------------------------------
-- Names and Operators
---------------------------------------------------------------------------------

instance PrettyAnn TyOpName where
  prettyAnn (MkTyOpName op) = prettyAnn op

instance PrettyAnn BinOp where
  prettyAnn (CustomOp op) = prettyAnn op
  prettyAnn UnionOp = unionSym
  prettyAnn InterOp = interSym

---------------------------------------------------------------------------------
-- Wrappers
---------------------------------------------------------------------------------

instance PrettyAnn (RST.VariantType pol) where
  prettyAnn varType = prettyAnn (embedVariantType varType)

instance PrettyAnn (RST.PrdCnsType pol) where
  prettyAnn pctype = prettyAnn (embedPrdCnsType pctype)

instance PrettyAnn CST.PrdCnsTyp where
  prettyAnn (CST.PrdType ty) = prettyAnn ty
  prettyAnn (CST.CnsType ty) = returnKw <+> prettyAnn ty

instance {-# OVERLAPPING #-} PrettyAnn (RST.LinearContext pol) where
  prettyAnn ctxt = prettyAnn (embedLinearContext ctxt)

instance {-# OVERLAPPING #-} PrettyAnn CST.LinearContext where
  prettyAnn ctxt = parens' comma (prettyAnn <$> ctxt)

instance PrettyAnn (RST.XtorSig pol) where
  prettyAnn xtorSig = prettyAnn (embedXtorSig xtorSig)

instance PrettyAnn CST.XtorSig where
  prettyAnn (CST.MkXtorSig xt args) = prettyAnn xt <> prettyAnn args

---------------------------------------------------------------------------------
-- Typ
---------------------------------------------------------------------------------

instance PrettyAnn (RST.Typ pol) where
  prettyAnn typ = prettyAnn (embedType typ)

instance PrettyAnn CST.Typ where
  -- Top and Bottom lattice types
  prettyAnn CST.TyTop {} = topSym
  prettyAnn CST.TyBot {} = botSym
  -- Type Variables
  prettyAnn (CST.TyUniVar _ tv) = prettyAnn tv
  prettyAnn (CST.TySkolemVar _ tv) = prettyAnn tv
  -- Recursive types
  prettyAnn (CST.TyRec _ rv t) =
    parens (recSym <+> prettyAnn rv <> "." <> align (prettyAnn t))
  -- Nominal types
  prettyAnn (CST.TyNominal _ tn args) =
    prettyAnn tn <> parens' commaSym (prettyAnn <$> args)
  -- Type operators
  prettyAnn (CST.TyBinOp _ t1 op t2) =
    parens $ prettyAnn t1 <+> prettyAnn op <+> prettyAnn t2
  prettyAnn (CST.TyBinOpChain ty tys) =
    let
      f (_loc,op,ty) = prettyAnn op <+> prettyAnn ty
    in
      prettyAnn ty <> hsep (NE.toList (f <$> tys))
  -- Structural data and codata types
  prettyAnn (CST.TyXData _ Data   xtors) =
    angles' commaSym  (prettyAnn <$> xtors)
  prettyAnn (CST.TyXData _ Codata xtors) =
    braces' commaSym (prettyAnn <$> xtors)
  -- Refinement types
  prettyAnn (CST.TyXRefined _ Data   tn xtors) =
    angles' mempty [prettyAnn tn <+> pipeSym, hsep (intersperse commaSym (prettyAnn <$> xtors))]
  prettyAnn (CST.TyXRefined _ Codata tn xtors) =
    braces' mempty [prettyAnn tn <+> pipeSym, hsep (intersperse commaSym (prettyAnn <$> xtors))]
  -- Primitive types
  prettyAnn (CST.TyPrim _ pt) = "#" <> prettyAnn pt
  prettyAnn (CST.TyParens _ ty) = parens (prettyAnn ty)


---------------------------------------------------------------------------------
-- TypScheme
---------------------------------------------------------------------------------

instance PrettyAnn (RST.TypeScheme pol) where
  prettyAnn tys = prettyAnn (embedTypeScheme tys)

instance PrettyAnn CST.TypeScheme where
  prettyAnn CST.TypeScheme { ts_vars = [], ts_monotype } =
    prettyAnn ts_monotype
  prettyAnn CST.TypeScheme { ts_vars, ts_monotype } =
    forallSym <+>
    sep (prettyAnn <$> ts_vars ) <>
    "." <+>
    prettyAnn ts_monotype
