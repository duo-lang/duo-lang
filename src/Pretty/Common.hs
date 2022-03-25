module Pretty.Common where

import Prettyprinter
import Text.Megaparsec.Pos

import Pretty.Pretty
import Syntax.Common
import Utils

---------------------------------------------------------------------------------
-- Locations
---------------------------------------------------------------------------------

instance PrettyAnn Pos where
  prettyAnn p = pretty (unPos p)

instance PrettyAnn Loc where
  prettyAnn (Loc (SourcePos fp line1 column1) (SourcePos _ line2 column2)) =
    pretty fp <> ":" <> prettyAnn line1 <> ":" <> prettyAnn column1 <> "-" <> prettyAnn line2 <> ":" <> prettyAnn column2

prettyMaybeLoc :: Maybe Loc -> Doc Annotation
prettyMaybeLoc Nothing = mempty
prettyMaybeLoc (Just loc) = prettyAnn loc <> ": "

---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

instance PrettyAnn XtorName where
  prettyAnn (MkXtorName xt) = annXtorName $ prettyAnn xt

instance PrettyAnn FreeVarName where
  prettyAnn (MkFreeVarName nm) = prettyAnn nm

instance PrettyAnn (Maybe FreeVarName) where
  prettyAnn Nothing = "_"
  prettyAnn (Just fv) = prettyAnn fv

instance PrettyAnn ModuleName where
  prettyAnn (MkModuleName nm) = prettyAnn nm

instance PrettyAnn TVar where
  prettyAnn (MkTVar tv) = prettyAnn tv

instance PrettyAnn TypeName where
  prettyAnn (MkTypeName tn) = annTypeName (pretty tn)

---------------------------------------------------------------------------------
-- Producer/Consumer and Arity
---------------------------------------------------------------------------------

instance PrettyAnn PrdCns where
  prettyAnn Prd = "Prd"
  prettyAnn Cns = "Cns"

prettyArity :: Arity -> Doc Annotation
prettyArity [] = mempty
prettyArity (Prd:rest) = parens "-" <> prettyArity rest
prettyArity (Cns:rest) = brackets "-" <> prettyArity rest

prettyPrdCnsRep :: PrdCnsRep pc -> Doc Annotation
prettyPrdCnsRep PrdRep = "[*]"
prettyPrdCnsRep CnsRep = "(*)"

---------------------------------------------------------------------------------
-- Data/Codata
---------------------------------------------------------------------------------

instance PrettyAnn DataCodata where
  prettyAnn Data = annKeyword "data"
  prettyAnn Codata = annKeyword "codata"

---------------------------------------------------------------------------------
-- Primitives
---------------------------------------------------------------------------------

instance PrettyAnn PrimitiveType where
  prettyAnn I64 = "I64"
  prettyAnn F64 = "F64"

instance PrettyAnn PrimitiveLiteral where
  prettyAnn (I64Lit n) = annLiteral (prettyAnn n) <> annTypeName "#I64"
  prettyAnn (F64Lit n) = annLiteral (prettyAnn n) <> annTypeName "#F64"

---------------------------------------------------------------------------------
-- Kinds
---------------------------------------------------------------------------------

instance PrettyAnn EvaluationOrder where
  prettyAnn CBV = annKeyword "CBV"
  prettyAnn CBN = annKeyword "CBN"

instance PrettyAnn MonoKind where
  prettyAnn (CBox eo)  = prettyAnn eo
  prettyAnn (CRep I64) = "I64Rep"
  prettyAnn (CRep F64) = "F64Rep"

instance PrettyAnn Variance where
  prettyAnn Covariant     = annSymbol "+"
  prettyAnn Contravariant = annSymbol "-"

instance PrettyAnn PolyKind where
  prettyAnn MkPolyKind { contravariant, covariant, returnKind } =
    parens' comma ((prettyTParam Contravariant <$> contravariant) ++ (prettyTParam Covariant <$> covariant)) <+> annSymbol "->" <+> prettyAnn returnKind

prettyTParam :: Variance -> (TVar, MonoKind) -> Doc Annotation
prettyTParam v (tv, k) = prettyAnn v <> prettyAnn tv <+> ":" <+> prettyAnn k
