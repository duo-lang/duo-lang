{-# LANGUAGE OverloadedStrings #-}
module Pretty.Constraints () where

import Prettyprinter
import qualified Data.Map as M

import Pretty.Pretty
import Pretty.Types ()
import Syntax.Types
---------------------------------------------------------------------------------
-- Prettyprinting of constraints, constraint sets and solved constraints.
---------------------------------------------------------------------------------

instance PrettyAnn (Constraint a) where
  prettyAnn (SubType _ t1 t2) =
    prettyAnn t1 <+> "<:" <+> prettyAnn t2

instance PrettyAnn (ConstraintSet a) where
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

