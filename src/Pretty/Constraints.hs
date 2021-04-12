{-# LANGUAGE OverloadedStrings #-}
module Pretty.Constraints () where

import Prettyprinter
import qualified Data.Map as M
import Text.Megaparsec.Pos

import Pretty.Pretty
import Pretty.Types ()
import Syntax.Types
import Utils

---------------------------------------------------------------------------------
-- Prettyprinting of constraints, constraint sets and solved constraints.
---------------------------------------------------------------------------------

instance PrettyAnn Pos where
  prettyAnn p = pretty (unPos p)

instance PrettyAnn Loc where
  prettyAnn (Loc (SourcePos fp line1 column1) (SourcePos _ line2 column2)) =
    pretty fp <> ":" <> prettyAnn line1 <> ":" <> prettyAnn column1 <> "-" <> prettyAnn line2 <> ":" <> prettyAnn column2

instance PrettyAnn ConstraintInfo where
  prettyAnn (Primary loc) = parens ("at" <+> prettyAnn loc)
  prettyAnn Recursive = parens "Recursive"
  prettyAnn Derived = parens "Derived"

instance PrettyAnn (Constraint ConstraintInfo) where
  prettyAnn (SubType ann t1 t2) =
    prettyAnn t1 <+> "<:" <+> prettyAnn t2 <+> prettyAnn ann

instance PrettyAnn ConstraintSet where
  prettyAnn ConstraintSet { cs_constraints, cs_uvars } = vsep
    [ "---------------------------------------------------------"
    , "                    ConstraintSet"
    , "---------------------------------------------------------"
    , "Generated unification variables:"
    , nest 3 (line' <> vsep (prettyAnn <$> cs_uvars))
    , ""
    , "Generated constraints:"
    , nest 3 (line' <> vsep (prettyAnn <$> cs_constraints))
    , ""
    , "---------------------------------------------------------"
    ]


printLowerBounds :: [Typ 'Pos] -> Doc Annotation
printLowerBounds [] = mempty
printLowerBounds lowerbounds =
  vsep [ "Lower bounds:"
       , nest 3 (line' <> vsep (prettyAnn <$> lowerbounds) <> line') ]

printUpperBounds :: [Typ 'Neg] -> Doc Annotation
printUpperBounds [] = mempty
printUpperBounds upperbounds =
  vsep [ "Upper bounds:"
       , nest 3 (line' <> vsep (prettyAnn <$> upperbounds) <> line') ]

instance PrettyAnn VariableState where
  prettyAnn VariableState { vst_lowerbounds , vst_upperbounds } =
    vsep [ printLowerBounds vst_lowerbounds
         , printUpperBounds vst_upperbounds
         ]

instance PrettyAnn SolverResult where
  prettyAnn solverResult = vsep
    [ "---------------------------------------------------------"
    , "                   Solved Constraints"
    , "---------------------------------------------------------"
    , vsep (solvedConstraintsToDoc <$> M.toList solverResult)
    , "---------------------------------------------------------"
    ]
    where
      solvedConstraintsToDoc :: (TVar,VariableState) -> Doc Annotation
      solvedConstraintsToDoc (v, vs) = vsep ["Type variable:" <+> prettyAnn v
                                            , nest 3 (line' <> prettyAnn vs)]

