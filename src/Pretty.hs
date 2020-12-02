{-# LANGUAGE OverloadedStrings #-}
module Pretty where
import qualified Data.Set as S

import Data.Graph.Inductive.Graph
import Data.GraphViz
import Data.Text.Lazy (pack)

import Syntax.Terms
import Syntax.Types
import Syntax.TypeGraph
import Utils

import Prettyprinter
import Prettyprinter.Render.String (renderString)

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

ppPrint :: Pretty a => a -> String
ppPrint doc = renderString (layoutPretty defaultLayoutOptions { layoutPageWidth = AvailablePerLine 100 1 }(pretty doc))

intercalateX :: Doc ann -> [Doc ann] -> Doc ann
intercalateX  x xs = cat (punctuate x xs)

intercalateComma :: [Doc ann] -> Doc ann
intercalateComma xs = cat (punctuate comma xs)

prettyTwice' :: (Pretty a, Pretty b) => [a] -> [b] -> Doc ann
prettyTwice' xs ys = xs' <> ys'
  where
    xs' = if null xs then mempty else parens   (intercalateComma (map pretty xs))
    ys' = if null ys then mempty else brackets (intercalateComma (map pretty ys))

prettyTwice :: Pretty a => Twice [a] -> Doc ann
prettyTwice (Twice xs ys) = prettyTwice' xs ys

---------------------------------------------------------------------------------
-- Prettyprinting of Terms
---------------------------------------------------------------------------------

instance Pretty XtorName where
  pretty xn = pretty (unXtorName xn)

instance Pretty a => Pretty (Case a) where
  pretty MkCase{..} = pretty case_name <> prettyTwice (fmap (const "-") case_args) <+> "=>" <+> pretty case_cmd

instance Pretty a => Pretty (XtorArgs a) where
  pretty (MkXtorArgs prds cns) = prettyTwice' prds cns

instance Pretty a => Pretty (Term pc a) where
  pretty (BoundVar _ (i,j)) = parens (pretty i <> "," <> pretty j)
  pretty (FreeVar _ v a) = parens (pretty v <+> ":" <+> pretty a)
  pretty (XtorCall _ xt args) = pretty xt <> pretty args
  pretty (Match PrdRep cases) = "comatch" <+> braces (group (nest 3 (line' <> vsep (punctuate comma (pretty <$> cases)))))
  pretty (Match CnsRep cases) = "match"   <+> braces (group (nest 3 (line' <> vsep (punctuate comma (pretty <$> cases)))))
  pretty (MuAbs pc a cmd) =
    case pc of {PrdRep -> "mu"; CnsRep -> "mu*"} <> brackets (pretty a) <> "." <> parens (pretty cmd)

instance Pretty a => Pretty (Command a) where
  pretty Done = "Done"
  pretty (Print t) = "Print" <+> pretty t
  pretty (Apply t1 t2) = group (nest 3 (line' <> vsep [pretty t1, ">>", pretty t2]))

---------------------------------------------------------------------------------
-- Prettyprinting of Types
---------------------------------------------------------------------------------

instance Pretty UVar where
  pretty (MkUVar n) = "U" <> pretty n

instance Pretty TVar where
  pretty (MkTVar tv) = pretty tv

instance Pretty RVar where
  pretty (MkRVar rv) = pretty rv

instance Pretty DataCodata where
  pretty Data = "+"
  pretty Codata = "-"

instance Pretty a => Pretty (XtorSig a) where
  pretty (MkXtorSig xt args) = pretty xt <> prettyTwice args

instance Pretty SimpleType where
  pretty (TyVar uvar) = pretty uvar
  pretty (SimpleType s xtors) = braces (pretty s <+> intercalateComma (pretty <$> xtors) <+> pretty s)

instance Pretty TargetType where
  pretty (TTyUnion []) = "Bot"
  pretty (TTyUnion [t]) = pretty t
  pretty (TTyUnion tts) = parens (intercalateX " \\/ " (map pretty tts))
  pretty (TTyInter []) = "Top"
  pretty (TTyInter [t]) = pretty t
  pretty (TTyInter tts) = parens (intercalateX " /\\ " (map pretty tts))
  pretty (TTyTVar tv) = pretty tv
  pretty (TTyRVar tv) = pretty tv
  pretty (TTyRec tv t) = "rec " <> pretty tv <> "." <> pretty t
  pretty (TTySimple s xtors) = braces (pretty s <+> intercalateComma (pretty <$> xtors) <+> pretty s)

instance Pretty TypeScheme where
  pretty (TypeScheme [] ty) = pretty ty
  pretty (TypeScheme tvs ty) = "forall " <> intercalateX "" (map pretty tvs) <> ". " <> pretty ty

instance Pretty Constraint where
  pretty (SubType t1 t2) = pretty t1 <+> "<:" <+> pretty t2

---------------------------------------------------------------------------------
-- Prettyprinting of Errors
---------------------------------------------------------------------------------

instance Pretty Error where
  pretty (ParseError err) = "Parsing error:" <+> pretty err
  pretty (EvalError err) = "Evaluation error:" <+> pretty err
  pretty (GenConstraintsError err) = "Constraint generation error:" <+> pretty err
  pretty (SolveConstraintsError err) = "Constraint solving error:" <+> pretty err

---------------------------------------------------------------------------------
-- Prettyprinting of Type Automata
---------------------------------------------------------------------------------

instance Pretty HeadCons where
  pretty (HeadCons maybeDat maybeCodat) =
    case maybeDat of
      Just dat -> "{+ " <> intercalateComma (pretty <$> S.toList dat) <> " +}"
        <> case maybeCodat of
          Just codat -> "; {- " <> intercalateComma (pretty <$> S.toList codat) <> " -}"
          Nothing -> ""
      Nothing -> case maybeCodat of
        Just codat -> "{- " <> intercalateComma (pretty <$> S.toList codat) <> " -}"
        Nothing -> ""

instance Pretty EdgeLabel where
  pretty (EdgeSymbol s xt pc i) =
    let
      showS = case s of {Data -> "+"; Codata -> "-"}
      showPc = case pc of {Prd -> "prd"; Cns -> "cns"}
    in
      showS <> pretty xt <> "." <> showPc <> "." <> pretty i

typeAutToDot :: TypeAut' EdgeLabel f -> DotGraph Node
typeAutToDot TypeAut {..} =
    let
      grWithFlow = insEdges [(i,j,Nothing) | (i,j) <- ta_flowEdges] (emap Just ta_gr)
    in
      graphToDot typeAutParams grWithFlow

typeAutParams :: GraphvizParams Node NodeLabel (Maybe EdgeLabel) () NodeLabel
typeAutParams = defaultParams
  { fmtNode = \(_,(pol,hc)) ->
    [ style filled
    , fillColor $ case pol of {Pos -> White; Neg -> Gray}
    , textLabel (pack (ppPrint (hc :: HeadCons)))]
  , fmtEdge = \(_,_,elM) -> case elM of {Nothing -> [arrowTo dotArrow]; Just el -> [textLabel $ pack (ppPrint (el :: EdgeLabel))] }
  }
