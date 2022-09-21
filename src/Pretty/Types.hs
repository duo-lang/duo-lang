module Pretty.Types where

import Data.List (intersperse)
import Data.List.NonEmpty qualified as NE
import Prettyprinter

import Pretty.Common ()
import Pretty.Pretty
import Syntax.RST.Types qualified as RST
import Syntax.CST.Types qualified as CST
import Syntax.TST.Types qualified as TST
import Syntax.CST.Names
import Resolution.Unresolve (Unresolve (..))
import Translate.EmbedTST (EmbedTST(..))

---------------------------------------------------------------------------------
-- Symbols used in the prettyprinting of types
---------------------------------------------------------------------------------
  
botSym :: Doc Annotation
botSym = annKeyword "Bot"

botSymUnicode :: Doc Annotation
botSymUnicode = annKeyword "⊥"

topSym :: Doc Annotation
topSym = annKeyword "Top"

topSymUnicode :: Doc Annotation
topSymUnicode = annKeyword "⊤"

unionSym :: Doc Annotation
unionSym = annKeyword "\\/"

unionSymUnicode :: Doc Annotation
unionSymUnicode = "∨"

interSym :: Doc Annotation
interSym = annKeyword "/\\"

interSymUnicode :: Doc Annotation
interSymUnicode = annKeyword "∧"

recSym :: Doc Annotation
recSym = annKeyword "rec"

forallSym :: Doc Annotation
forallSym = annKeyword "forall"

forallSymUnicode :: Doc Annotation
forallSymUnicode = annKeyword "∀"

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
  prettyAnn UnionOp = unionSymUnicode
  prettyAnn InterOp = interSymUnicode

instance PrettyAnn CST.DataCodata where
  prettyAnn CST.Data = annKeyword "data"
  prettyAnn CST.Codata = annKeyword "codata"

--------------------------------------------------------------C-------------------
-- Wrappers
---------------------------------------------------------------------------------

instance PrettyAnn (RST.VariantType pol) where
  prettyAnn varType = prettyAnn (unresolve varType)

instance PrettyAnn (RST.PrdCnsType pol) where
  prettyAnn pctype = prettyAnn (unresolve pctype)

instance PrettyAnn (TST.PrdCnsType pol) where 
  prettyAnn pctype = prettyAnn (embedTST pctype)

instance PrettyAnn CST.PrdCnsTyp where
  prettyAnn (CST.PrdType ty) = prettyAnn ty
  prettyAnn (CST.CnsType ty) = returnKw <+> prettyAnn ty

instance {-# OVERLAPPING #-} PrettyAnn (RST.LinearContext pol) where
  prettyAnn ctxt = prettyAnn (unresolve ctxt)

instance {-# OVERLAPPING #-} PrettyAnn CST.LinearContext where
  prettyAnn ctxt = parens' comma (prettyAnn <$> ctxt)
 
instance {-# OVERLAPPING #-} PrettyAnn (TST.LinearContext pol) where 
  prettyAnn ctxt = parens' comma (prettyAnn <$> ctxt)

instance PrettyAnn (RST.XtorSig pol) where
  prettyAnn xtorSig = prettyAnn (unresolve xtorSig)

instance PrettyAnn (TST.XtorSig pol) where
  prettyAnn xtorSig = prettyAnn (embedTST xtorSig)

instance PrettyAnn CST.XtorSig where
  prettyAnn (CST.MkXtorSig xt args) = prettyAnn xt <> prettyAnn args

---------------------------------------------------------------------------------
-- Typ
---------------------------------------------------------------------------------

instance PrettyAnn (RST.Typ pol) where
  prettyAnn typ = prettyAnn (unresolve typ)

instance PrettyAnn (TST.Typ pol) where
  prettyAnn typ = prettyAnn (embedTST typ)

instance PrettyAnn CST.Typ where
  -- Top and Bottom lattice types
  prettyAnn CST.TyTop {} = topSymUnicode
  prettyAnn CST.TyBot {} = botSymUnicode
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
  prettyAnn tys = prettyAnn (unresolve tys)

instance PrettyAnn (TST.TypeScheme pol) where
  prettyAnn tys = prettyAnn (embedTST tys)

instance PrettyAnn CST.TypeScheme where
  prettyAnn CST.TypeScheme { ts_vars = [], ts_monotype } =
    prettyAnn ts_monotype
  prettyAnn CST.TypeScheme { ts_vars, ts_monotype } =
    forallSymUnicode <+>
    sep (prettyAnn <$> ts_vars ) <>
    "." <+>
    prettyAnn ts_monotype
