module Pretty.Types where

import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NE
import Prettyprinter

import Pretty.Pretty
import Syntax.CST.Types (BinOp(..))
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

arrowSym :: Doc Annotation
arrowSym = annKeyword "->"

parSym :: Doc Annotation
parSym = annKeyword "⅋"

---------------------------------------------------------------------------------
-- Prettyprinting of Kinds
---------------------------------------------------------------------------------

instance PrettyAnn CallingConvention  where
  prettyAnn CBV = "CBV"
  prettyAnn CBN = "CBN"

instance PrettyAnn KVar where
  prettyAnn kv = pretty (unKVar kv)

instance PrettyAnn Kind where
  prettyAnn (MonoKind eo) = "Type" <+> prettyAnn eo
  prettyAnn (KindVar var) = prettyAnn var

---------------------------------------------------------------------------------
-- Prettyprinting of types
---------------------------------------------------------------------------------

instance PrettyAnn BinOp where
  prettyAnn FunOp = arrowSym
  prettyAnn ParOp = parSym
  prettyAnn UnionOp = unionSym
  prettyAnn InterOp = interSym

resugarType :: Typ pol -> Maybe (Doc Annotation, BinOp, Doc Annotation)
resugarType (TyCodata _ Nothing [MkXtorSig (MkXtorName Structural "Ap") [PrdCnsType PrdRep tl, PrdCnsType CnsRep tr]]) = Just (prettyAnn tl , FunOp, prettyAnn tr)
resugarType (TyCodata _ Nothing [MkXtorSig (MkXtorName Structural "Par") [PrdCnsType PrdRep tl, PrdCnsType CnsRep tr]]) = Just (prettyAnn tl, ParOp, prettyAnn tr)
resugarType _ = Nothing

instance PrettyAnn Polarity where
  prettyAnn Pos = "Pos"
  prettyAnn Neg = "Neg"

instance PrettyAnn TVar where
  prettyAnn (MkTVar tv) = pretty tv

instance PrettyAnn (Typ pol) where
  -- Sugared types
  prettyAnn (resugarType -> Just (ty1, binOp, ty2)) = parens (ty1 <+> prettyAnn binOp <+> ty2)
  -- Lattice types
  prettyAnn (TySet PosRep _ [])  = botSym
  prettyAnn (TySet PosRep _ [t]) = prettyAnn t
  prettyAnn (TySet PosRep _ tts) = parens' unionSym (map prettyAnn tts)
  prettyAnn (TySet NegRep _ [])  = topSym
  prettyAnn (TySet NegRep _ [t]) = prettyAnn t
  prettyAnn (TySet NegRep _ tts) = parens' interSym (map prettyAnn tts)
  -- Type Variables
  prettyAnn (TyVar _ _ tv)       = prettyAnn tv
  -- Recursive types
  prettyAnn (TyRec _ rv t)       = recSym <+> prettyAnn rv <> "." <> align (prettyAnn t)
  -- Nominal types
  prettyAnn (TyNominal _ _ tn)   = prettyAnn tn
  -- Structural data and codata types
  prettyAnn (TyData _ Nothing xtors)   = angles' pipeSym  (prettyAnn <$> xtors)
  prettyAnn (TyCodata _ Nothing xtors) = braces' commaSym (prettyAnn <$> xtors)
  -- Refinement types
  prettyAnn (TyData pr (Just tn) xtors)   = dbraces' mempty [prettyAnn tn <+> refinementSym, prettyAnn (TyData pr Nothing xtors)]
  prettyAnn (TyCodata pr (Just tn) xtors) = dbraces' mempty [prettyAnn tn <+> refinementSym, prettyAnn (TyCodata pr Nothing xtors)]
  
instance PrettyAnn (PrdCnsType pol) where
  prettyAnn (PrdCnsType _ ty) = prettyAnn ty

splitCtxt :: LinearContext pol -> [NonEmpty (PrdCnsType pol)]
splitCtxt = NE.groupBy f
  where
    f :: PrdCnsType pol -> PrdCnsType pol -> Bool
    f (PrdCnsType PrdRep _) (PrdCnsType PrdRep _) = True
    f (PrdCnsType CnsRep _) (PrdCnsType CnsRep _) = True
    f (PrdCnsType _ _) (PrdCnsType _ _) = False

printSegment :: NonEmpty (PrdCnsType pol) -> Doc Annotation
printSegment (PrdCnsType PrdRep ty :| rest) = parens'   comma (prettyAnn <$> PrdCnsType PrdRep ty : rest)
printSegment (PrdCnsType CnsRep ty :| rest) = brackets' comma (prettyAnn <$> PrdCnsType CnsRep ty : rest)

prettyTvarKind :: (TVar, Kind) -> Doc Annotation
prettyTvarKind (tv,kind) = parens (prettyAnn tv <+> ":" <+> prettyAnn kind)

instance {-# OVERLAPPING #-} PrettyAnn (LinearContext pol) where
  prettyAnn ctxt = mconcat (printSegment <$> splitCtxt ctxt)

instance PrettyAnn (XtorSig a) where
  prettyAnn (MkXtorSig xt args) = prettyAnn xt <> prettyAnn args

instance PrettyAnn (TypeScheme pol) where
  prettyAnn (TypeScheme [] ty) =
    prettyAnn ty
  prettyAnn (TypeScheme tvs ty) =
    forallSym <+> sep (prettyTvarKind <$> tvs) <> "." <+> prettyAnn ty

instance PrettyAnn TypeName where
  prettyAnn (MkTypeName tn) = annTypeName (pretty tn)

