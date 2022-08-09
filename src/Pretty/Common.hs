module Pretty.Common where

import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Prettyprinter
import Text.Megaparsec.Pos

import Pretty.Pretty
import Syntax.Common.Names
    ( Associativity(..),
      ClassName(MkClassName),
      DocComment(unDocComment),
      FreeVarName(MkFreeVarName),
      MethodName(MkMethodName),
      ModuleName(MkModuleName),
      Precedence(..),
      RecTVar(MkRecTVar),
      RnTypeName(MkRnTypeName, rnTnName),
      SkolemTVar(MkSkolemTVar),
      TypeName(MkTypeName),
      UniTVar(MkUniTVar),
      XtorName(MkXtorName) )
import Syntax.Common.PrdCns ( Arity, PrdCns(..) )
import Syntax.Common.Types ( NominalStructural(..) )
import Syntax.Common.Primitives ( PrimitiveType(..) )
import Syntax.Common.Kinds
    ( EvaluationOrder(..), MonoKind(..), PolyKind(..), Variance(..) )
import Utils ( Loc(..) )


instance PrettyAnn a => PrettyAnn (NonEmpty a) where
  prettyAnn ne = vsep (prettyAnn <$> NE.toList ne)
---------------------------------------------------------------------------------
-- Locations
---------------------------------------------------------------------------------

instance PrettyAnn Pos where
  prettyAnn p = pretty (unPos p)

instance PrettyAnn Loc where
  prettyAnn (Loc (SourcePos fp line1 column1) (SourcePos _ line2 column2)) =
    pretty fp <> ":" <> prettyAnn line1 <> ":" <> prettyAnn column1 <> "-" <> prettyAnn line2 <> ":" <> prettyAnn column2

---------------------------------------------------------------------------------
-- Comments
---------------------------------------------------------------------------------

instance PrettyAnn DocComment where
  prettyAnn doc = pretty (unDocComment doc)

---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

instance PrettyAnn XtorName where
  prettyAnn (MkXtorName xt) = annXtorName $ prettyAnn xt

instance PrettyAnn MethodName where
  prettyAnn (MkMethodName xt) = annMethodName $ prettyAnn xt

instance PrettyAnn ClassName where
  prettyAnn (MkClassName xt) = annClassName $ prettyAnn xt

instance PrettyAnn FreeVarName where
  prettyAnn (MkFreeVarName nm) = prettyAnn nm

instance PrettyAnn ModuleName where
  prettyAnn (MkModuleName nm) = prettyAnn nm

instance PrettyAnn UniTVar where
  prettyAnn (MkUniTVar tv) = prettyAnn tv

instance PrettyAnn SkolemTVar where
  prettyAnn (MkSkolemTVar tv) = prettyAnn tv

instance PrettyAnn RecTVar where 
  prettyAnn (MkRecTVar tv) = prettyAnn tv

instance PrettyAnn TypeName where
  prettyAnn (MkTypeName tn) = annTypeName (pretty tn)

instance PrettyAnn RnTypeName where
  prettyAnn MkRnTypeName { rnTnName } = prettyAnn rnTnName

instance PrettyAnn Precedence where
  prettyAnn (MkPrecedence i) = pretty i

instance PrettyAnn Associativity where
  prettyAnn LeftAssoc = "leftassoc"
  prettyAnn RightAssoc = "rightassoc"

---------------------------------------------------------------------------------
-- Producer/Consumer and Arity
---------------------------------------------------------------------------------

instance PrettyAnn PrdCns where
  prettyAnn Prd = "Prd"
  prettyAnn Cns = "Cns"

prettyArity :: Arity -> Doc Annotation
prettyArity [] = mempty
prettyArity (Prd:rest) = parens "-" <> prettyArity rest
prettyArity (Cns:rest) = parens "-" <> prettyArity rest

prettyPrdCns :: PrdCns -> Doc Annotation
prettyPrdCns Prd = "prd"
prettyPrdCns Cns = "cns"

---------------------------------------------------------------------------------
-- Data/Codata and Nominal/Structural/Refinement
---------------------------------------------------------------------------------

instance PrettyAnn NominalStructural where
  prettyAnn Nominal = "Nominal"
  prettyAnn Structural = "Structural"
  prettyAnn Refinement = "Refinement"

---------------------------------------------------------------------------------
-- Primitives
---------------------------------------------------------------------------------

instance PrettyAnn PrimitiveType where
  prettyAnn I64 = "I64"
  prettyAnn F64 = "F64"
  prettyAnn PChar = "Char"
  prettyAnn PString = "String"

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
  prettyAnn (CRep PChar) = "CharRep"
  prettyAnn (CRep PString) = "StringRep"

instance PrettyAnn Variance where
  prettyAnn Covariant     = annSymbol "+"
  prettyAnn Contravariant = annSymbol "-"

instance PrettyAnn PolyKind where
  prettyAnn MkPolyKind { kindArgs = [], returnKind } =
    prettyAnn returnKind
  prettyAnn MkPolyKind { kindArgs, returnKind } =
    parens' comma (prettyTParam <$> kindArgs) <+>
    annSymbol "->" <+>
    prettyAnn returnKind

prettyTParam :: (Variance, SkolemTVar, MonoKind) -> Doc Annotation
prettyTParam (v, tv, k) = prettyAnn v <> prettyAnn tv <+> annSymbol ":" <+> prettyAnn k
