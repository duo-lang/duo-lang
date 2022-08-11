module Pretty.Types where

import Data.List (intersperse)
import Data.List.NonEmpty qualified as NE
import Prettyprinter

import Pretty.Common ()
import Pretty.Pretty
import Syntax.RST.Types qualified as RST
import Syntax.CST.Types qualified as CST
import Syntax.Common.Names
import Syntax.Common.Primitives
import Translate.Reparse

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

instance PrettyAnn CST.DataCodata where
  prettyAnn CST.Data = annKeyword "data"
  prettyAnn CST.Codata = annKeyword "codata"

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
instance PrettyAnn PrimitiveType where
  prettyAnn I64 = "I64"
  prettyAnn F64 = "F64"
  prettyAnn PChar = "Char"
  prettyAnn PString = "String"

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
  prettyAnn (CST.TyXData _ CST.Data   xtors) =
    angles' commaSym  (prettyAnn <$> xtors)
  prettyAnn (CST.TyXData _ CST.Codata xtors) =
    braces' commaSym (prettyAnn <$> xtors)
  -- Refinement types
  prettyAnn (CST.TyXRefined _ CST.Data   tn xtors) =
    angles' mempty [prettyAnn tn <+> pipeSym, hsep (intersperse commaSym (prettyAnn <$> xtors))]
  prettyAnn (CST.TyXRefined _ CST.Codata tn xtors) =
    braces' mempty [prettyAnn tn <+> pipeSym, hsep (intersperse commaSym (prettyAnn <$> xtors))]
  -- Primitive types
  prettyAnn (CST.TyI64 _) = "#I64"
  prettyAnn (CST.TyF64 _) = "#F64"
  prettyAnn (CST.TyChar _) = "#Char"
  prettyAnn (CST.TyString _) = "#String"
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
