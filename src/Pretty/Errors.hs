{-# LANGUAGE OverloadedStrings #-}
module Pretty.Errors where

import Text.Megaparsec.Pos
import Prettyprinter

import Pretty.Pretty
import Utils

---------------------------------------------------------------------------------
-- Prettyprinting of Errors
---------------------------------------------------------------------------------

instance PrettyAnn Error where
  prettyAnn (ParseError err) = "Parsing error:" <+> pretty err
  prettyAnn (EvalError err) = "Evaluation error:" <+> pretty err
  prettyAnn (GenConstraintsError err) = "Constraint generation error:" <+> pretty err
  prettyAnn (SolveConstraintsError err) = "Constraint solving error:" <+> pretty err
  prettyAnn (TypeAutomatonError err) = "Type simplification error:" <+> pretty err
  prettyAnn (OtherError err) = "Other Error:" <+> pretty err

instance PrettyAnn Pos where
  prettyAnn p = pretty (unPos p)

instance PrettyAnn Loc where
  prettyAnn (Loc (SourcePos fp line1 column1) (SourcePos _ line2 column2)) =
    pretty fp <> ":" <> prettyAnn line1 <> ":" <> prettyAnn column1 <> "-" <> prettyAnn line2 <> ":" <> prettyAnn column2

instance PrettyAnn LocatedError where
  prettyAnn (Located loc err) = vsep ["Error at:" <+> prettyAnn loc, prettyAnn err]


