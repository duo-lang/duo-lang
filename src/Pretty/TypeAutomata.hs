{-# LANGUAGE OverloadedStrings #-}
module Pretty.TypeAutomata ( typeAutToDot ) where

import Data.Graph.Inductive.Graph
import Data.GraphViz.Attributes.Complete (Attribute(Style), StyleName(Dashed), StyleItem(SItem))
import Data.GraphViz
import Data.Maybe (catMaybes)
import qualified Data.Set as S
import Data.Text.Lazy (pack)
import Prettyprinter

import Pretty.Pretty
import Syntax.Terms
import Syntax.TypeGraph


---------------------------------------------------------------------------------
-- Prettyprinting of Type Automata
---------------------------------------------------------------------------------

instance Pretty NodeLabel where
  pretty (HeadCons _ maybeDat maybeCodat tns) = intercalateX ";" (catMaybes [printDat <$> maybeDat
                                                                          , printCodat <$> maybeCodat
                                                                          , printNominal tns])
    where
      printDat   dat   = angles (mempty <+> cat (punctuate " | " (pretty <$> (S.toList dat))) <+> mempty)
      printCodat codat = braces (mempty <+> cat (punctuate " , " (pretty <$> (S.toList codat))) <+> mempty)
      printNominal tns = Just (intercalateX ";" (pretty <$> (S.toList tns)))

instance Pretty (EdgeLabel a) where
  pretty (EdgeSymbol _ xt Prd i) = pretty xt <> parens (pretty i)
  pretty (EdgeSymbol _ xt Cns i) = pretty xt <> brackets (pretty i)
  pretty (EpsilonEdge _) = "e"

typeAutToDot :: TypeAut' EdgeLabelNormal f -> DotGraph Node
typeAutToDot TypeAut {..} =
    let
      grWithFlow = insEdges [(i,j,EpsilonEdge ()) | (i,j) <- ta_flowEdges] (emap embedEdgeLabel ta_gr) -- Should be modified!
    in
      graphToDot typeAutParams grWithFlow

typeAutParams :: GraphvizParams Node NodeLabel EdgeLabelEpsilon () NodeLabel
typeAutParams = defaultParams
  { fmtNode = \(_,nl) ->
    [ style filled
    , fillColor $ case hc_pol nl of {Prd -> White; Cns -> Gray}
    , textLabel (pack (ppPrint (nl :: NodeLabel)))]
  , fmtEdge = \(_,_,elM) -> case elM of
                              el@(EdgeSymbol _ _ _ _) -> regularEdgeStyle el
                              (EpsilonEdge _) -> flowEdgeStyle
  }
  where
    flowEdgeStyle = [arrowTo dotArrow, Style [SItem Dashed []]]
    regularEdgeStyle el = [textLabel $ pack (ppPrint el)]
