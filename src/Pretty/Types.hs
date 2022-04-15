module Pretty.Types where

import Data.List (intersperse)
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
  prettyAnn RST.TyTop {}               = topSym
  prettyAnn RST.TyBot {}               = botSym
  prettyAnn (RST.TyUnion _ _ ty ty')   = parens' unionSym [prettyAnn ty, prettyAnn ty']
  prettyAnn (RST.TyInter _ _ ty ty')   = parens' interSym [prettyAnn ty, prettyAnn ty']
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
  prettyAnn (RST.PrdCnsType PrdRep ty) = prettyAnn ty
  prettyAnn (RST.PrdCnsType CnsRep ty) = "return " <> prettyAnn ty

instance {-# OVERLAPPING #-} PrettyAnn (RST.LinearContext pol) where
  prettyAnn ctxt = parens'   comma (prettyAnn <$> ctxt)

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
