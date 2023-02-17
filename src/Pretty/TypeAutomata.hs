module Pretty.TypeAutomata ( typeAutToDot ) where

import Data.Graph.Inductive.Graph
import Data.GraphViz.Attributes.Complete (Attribute(Style), StyleName(Dashed,Dotted), StyleItem(SItem))
import Data.GraphViz
import Data.Maybe (catMaybes)
import Data.Set qualified as S
import Data.Map qualified as M
import Data.Text.Lazy (pack)
import Prettyprinter

import Pretty.Pretty (ppPrintString, PrettyAnn(..), intercalateX)
import Pretty.Common
import Pretty.Types (pipeSym)
import TypeAutomata.Definition
import Syntax.CST.Types (PrdCns(..))
import Syntax.RST.Types (Polarity(..))

---------------------------------------------------------------------------------
-- Prettyprinting of Type Automata
---------------------------------------------------------------------------------

instance PrettyAnn XtorLabel where
  prettyAnn lbl =
    prettyAnn lbl.labelName <> prettyArity lbl.labelArity

instance PrettyAnn PrimitiveType where
  prettyAnn I64 = "I64"
  prettyAnn F64 = "F64"
  prettyAnn PChar = "Char"
  prettyAnn PString = "String"

instance PrettyAnn NodeLabel where
  prettyAnn (MkPrimitiveNodeLabel _ tp) = prettyAnn tp
  prettyAnn (MkNodeLabel _ maybeDat maybeCodat tns refDat refCodat knd) =
    intercalateX ";" (catMaybes [printDat <$> maybeDat
                                , printCodat <$> maybeCodat
                                , printNominal tns
                                , printRefDat (fst refDat)
                                , printRefCodat (fst refCodat)
                                , Just $ prettyAnn knd])
    where
      printDat   dat   = mempty <+> cat (punctuate " , " (prettyAnn <$> S.toList dat)) <+> mempty
      printCodat codat = mempty <+> cat (punctuate " , " (prettyAnn <$> S.toList codat)) <+> mempty
      printNominal tnSet = case S.toList tnSet of
        [] -> Nothing
        tns -> Just (intercalateX ";" ((\(tn, _) -> prettyAnn tn) <$> tns))
      printRefDat refDat = case M.toList refDat of
        [] -> Nothing
        refTns -> Just $ intercalateX "; " $ (\(tn, (xtors,vars)) -> angles $ mempty <+>
          prettyAnn tn <+> pipeSym <+> printDat xtors <+> "@" <+> prettyAnn vars <+> mempty) <$> refTns
      printRefCodat refCodat = case M.toList refCodat of
        [] -> Nothing
        refTns -> Just $ intercalateX "; " $ (\(tn, (xtors,vars)) -> braces $ mempty <+>
          prettyAnn tn <+> pipeSym <+> printCodat xtors <+> "@" <+> prettyAnn vars <+> mempty) <$> refTns

instance PrettyAnn (EdgeLabel a) where
  prettyAnn (EdgeSymbol _ xt Prd i) = prettyAnn xt <> parens (pretty i)
  prettyAnn (EdgeSymbol _ xt Cns i) = prettyAnn xt <> brackets (pretty i)
  prettyAnn (EpsilonEdge _) = "e"
  prettyAnn (RefineEdge tn) = prettyAnn tn
  prettyAnn (TypeArgEdge tn v i) = "TypeArg" <> parens (prettyAnn tn <> " , " <> prettyAnn v <> " , " <> pretty i)

typeAutToDot :: Bool -> TypeAut' (EdgeLabel a) f pol -> DotGraph Node
typeAutToDot showId aut =
    let
      grWithFlow = insEdges [(i,j,EpsilonEdge (error "Never forced")) | (i,j) <- aut.ta_core.ta_flowEdges] aut.ta_core.ta_gr
    in
      graphToDot (typeAutParams showId) grWithFlow

typeAutParams :: Bool -> GraphvizParams Node NodeLabel (EdgeLabel a) () NodeLabel
typeAutParams showId = defaultParams
  { fmtNode = \(n,nl) ->
    [ style filled
    , fillColor $ case getPolarityNL nl of {Pos -> White; Neg -> Gray}
    , textLabel (pack ((if showId then show n <> ": " else "") <> ppPrintString (nl :: NodeLabel)))]
  , fmtEdge = \(_,_,elM) -> case elM of
                              el@EdgeSymbol {} -> regularEdgeStyle el
                              (EpsilonEdge _) -> flowEdgeStyle
                              RefineEdge tn -> refEdgeStyle tn
                              el@TypeArgEdge {} -> typeArgEdgeStyle el
  }
  where
    flowEdgeStyle = [arrowTo dotArrow, Style [SItem Dashed []]]
    regularEdgeStyle el = [textLabel $ pack (ppPrintString el)]
    refEdgeStyle tn = [arrowTo vee, Style [SItem Dotted []], textLabel $ pack $ ppPrintString tn]
    typeArgEdgeStyle el = [textLabel $ pack (ppPrintString el)]
