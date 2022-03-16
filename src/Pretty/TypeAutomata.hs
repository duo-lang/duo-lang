module Pretty.TypeAutomata ( typeAutToDot ) where

import Data.Graph.Inductive.Graph
import Data.GraphViz.Attributes.Complete (Attribute(Style), StyleName(Dashed,Dotted), StyleItem(SItem))
import Data.GraphViz
import Data.Maybe (catMaybes)
import Data.Set qualified as S
import Data.Map qualified as M
import Data.Text.Lazy (pack)
import Prettyprinter

import Pretty.Pretty (ppPrintString, PrettyAnn(..), intercalateX, Annotation)
import Pretty.Types (pipeSym)
import Syntax.Common
import TypeAutomata.Definition

---------------------------------------------------------------------------------
-- Prettyprinting of Type Automata
---------------------------------------------------------------------------------

prettyArity :: Arity -> Doc Annotation
prettyArity [] = mempty
prettyArity (Prd:rest) = parens "-" <> prettyArity rest
prettyArity (Cns:rest) = brackets "-" <> prettyArity rest

instance PrettyAnn XtorLabel where
  prettyAnn MkXtorLabel { labelName, labelArity } =
    prettyAnn labelName <> prettyArity labelArity

instance PrettyAnn NodeLabel where
  prettyAnn (MkNodeLabel _ maybeDat maybeCodat tns refDat refCodat) =
    intercalateX ";" (catMaybes [printDat <$> maybeDat
                                , printCodat <$> maybeCodat
                                , printNominal tns
                                , printRefDat refDat
                                , printRefCodat refCodat])
    where
      printDat   dat   = mempty <+> cat (punctuate " , " (prettyAnn <$> S.toList dat)) <+> mempty
      printCodat codat = mempty <+> cat (punctuate " , " (prettyAnn <$> S.toList codat)) <+> mempty
      printNominal tnSet = case S.toList tnSet of
        [] -> Nothing
        tns -> Just (intercalateX ";" ((\(tn, _, _) -> prettyAnn tn) <$> tns))
      printRefDat refDat = case M.toList refDat of
        [] -> Nothing
        refTns -> Just $ intercalateX "; " $ (\(key, content) -> angles $ mempty <+>
          prettyAnn key <+> pipeSym <+> printDat content <+> mempty) <$> refTns
      printRefCodat refCodat = case M.toList refCodat of
        [] -> Nothing
        refTns -> Just $ intercalateX "; " $ (\(key, content) -> braces $ mempty <+>
          prettyAnn key <+> pipeSym <+> printCodat content <+> mempty) <$> refTns

instance PrettyAnn (EdgeLabel a) where
  prettyAnn (EdgeSymbol _ xt Prd i) = prettyAnn xt <> parens (pretty i)
  prettyAnn (EdgeSymbol _ xt Cns i) = prettyAnn xt <> brackets (pretty i)
  prettyAnn (EpsilonEdge _) = "e"
  prettyAnn (RefineEdge tn) = prettyAnn tn
  prettyAnn (TypeArgEdge tn v i) = "TypeArg" <> parens (pretty (unTypeName tn) <> " , " <> prettyAnn v <> " , " <> pretty i)

typeAutToDot :: TypeAut' (EdgeLabel a) f pol -> DotGraph Node
typeAutToDot TypeAut {ta_core = TypeAutCore{..}} =
    let
      grWithFlow = insEdges [(i,j,EpsilonEdge (error "Never forced")) | (i,j) <- ta_flowEdges] ta_gr
    in
      graphToDot typeAutParams grWithFlow

typeAutParams :: GraphvizParams Node NodeLabel (EdgeLabel a) () NodeLabel
typeAutParams = defaultParams
  { fmtNode = \(_,nl) ->
    [ style filled
    , fillColor $ case nl_pol nl of {Pos -> White; Neg -> Gray}
    , textLabel (pack (ppPrintString (nl :: NodeLabel)))]
  , fmtEdge = \(_,_,elM) -> case elM of
                              el@(EdgeSymbol _ _ _ _) -> regularEdgeStyle el
                              (EpsilonEdge _) -> flowEdgeStyle
                              RefineEdge tn -> refEdgeStyle tn
                              el@(TypeArgEdge _ _ _) -> typeArgEdgeStyle el
  }
  where
    flowEdgeStyle = [arrowTo dotArrow, Style [SItem Dashed []]]
    regularEdgeStyle el = [textLabel $ pack (ppPrintString el)]
    refEdgeStyle tn = [arrowTo vee, Style [SItem Dotted []], textLabel $ pack $ ppPrintString tn]
    typeArgEdgeStyle el = [textLabel $ pack (ppPrintString el)]
