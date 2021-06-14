module Pretty.TypeAutomata ( typeAutToDot ) where

import Data.Graph.Inductive.Graph
import Data.GraphViz.Attributes.Complete (Attribute(Style), StyleName(Dashed), StyleName(Dotted), StyleItem(SItem))
import Data.GraphViz
import Data.Maybe (catMaybes)
import qualified Data.Set as S
import Data.Text.Lazy (pack)
import Prettyprinter

import Pretty.Pretty (ppPrintString, PrettyAnn(..), intercalateX)
import Pretty.Types ()
import Syntax.CommonTerm (PrdCns(..))
import TypeAutomata.Definition
import Syntax.Types


---------------------------------------------------------------------------------
-- Prettyprinting of Type Automata
---------------------------------------------------------------------------------

instance PrettyAnn XtorLabel where
  prettyAnn MkXtorLabel { labelName, labelPrdArity, labelCnsArity } =
    prettyAnn labelName <>
    parens (pretty labelPrdArity) <>
    brackets (pretty labelCnsArity)

instance PrettyAnn NodeLabel where
  prettyAnn (MkNodeLabel _ maybeDat maybeCodat tns) = intercalateX ";" (catMaybes [printDat <$> maybeDat
                                                                          , printCodat <$> maybeCodat
                                                                          , printNominal tns])
    where
      printDat   dat   = angles (mempty <+> cat (punctuate " | " (prettyAnn <$> (S.toList dat))) <+> mempty)
      printCodat codat = braces (mempty <+> cat (punctuate " , " (prettyAnn <$> (S.toList codat))) <+> mempty)
      printNominal tns = Just (intercalateX ";" (prettyAnn <$> (S.toList tns)))

instance PrettyAnn (EdgeLabel a) where
  prettyAnn (EdgeSymbol _ xt Prd i) = prettyAnn xt <> parens (pretty i)
  prettyAnn (EdgeSymbol _ xt Cns i) = prettyAnn xt <> brackets (pretty i)
  prettyAnn (EpsilonEdge _) = "e"
  prettyAnn RefineEdge = "ref"

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
                              RefineEdge -> refEdgeStyle
  }
  where
    flowEdgeStyle = [arrowTo dotArrow, Style [SItem Dashed []]]
    regularEdgeStyle el = [textLabel $ pack (ppPrintString el)]
    refEdgeStyle = [arrowTo dotArrow, Style [SItem Dotted []]]
