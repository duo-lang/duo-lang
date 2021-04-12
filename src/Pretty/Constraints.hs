{-# LANGUAGE OverloadedStrings #-}
module Pretty.Constraints where

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
    , nest 3 (line' <> hsep (prettyAnn <$> cs_uvars))
    , "Generated constraints:"
    , nest 3 (line' <> hsep (prettyAnn <$> cs_constraints))
    , "---------------------------------------------------------"
    ]

instance PrettyAnn VariableState where
  prettyAnn VariableState { vst_lowerbounds, vst_upperbounds } = vsep
    [ "Lower bounds:"
    , nest 3 (line' <> hsep (prettyAnn <$> vst_lowerbounds))
    , "Upper bounds:"
    , nest 3 (line' <> hsep (prettyAnn <$> vst_upperbounds))
    ]

instance PrettyAnn SolverResult where
  prettyAnn solverResult = hsep
    [ "---------------------------------------------------------"
    , "                   Solved Constraints"
    , "---------------------------------------------------------"
    , vsep (solvedConstraintsToDoc <$> M.toList solverResult)
    ]
    where
      solvedConstraintsToDoc :: (TVar,VariableState) -> Doc Annotation
      solvedConstraintsToDoc (v, vs) = hsep [prettyAnn v, prettyAnn vs]

