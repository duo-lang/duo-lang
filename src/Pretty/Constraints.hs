module Pretty.Constraints () where

import Prettyprinter
import Data.Map qualified as M
import Text.Megaparsec.Pos

import Pretty.Pretty
import Pretty.Types ()
import Syntax.Types
import TypeInference.Constraints
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
  -- Primary Constraints
  prettyAnn (CtorArgsConstraint loc) = parens ("Ctor args constraint at" <+> prettyAnn loc)
  prettyAnn (DtorArgsConstraint loc) = parens ("Dtor args constraint at" <+> prettyAnn loc)
  prettyAnn (CaseConstraint loc) = parens ("Case constraint at" <+> prettyAnn loc)
  prettyAnn (PatternMatchConstraint loc) = parens ("Pattern match constraint at" <+> prettyAnn loc)
  prettyAnn (DtorApConstraint loc) = parens ("DtorAp constraint at" <+> prettyAnn loc)
  prettyAnn (CommandConstraint loc) = parens ("Constraint from logical command at" <+> prettyAnn loc)
  prettyAnn RecursionConstraint = parens "Recursive"
  -- Derived Constraints
  prettyAnn UpperBoundConstraint           = parens "UpperBound"
  prettyAnn LowerBoundConstraint           = parens "LowerBound"
  prettyAnn XtorSubConstraint              = parens "XtorSubConstraint"
  prettyAnn IntersectionUnionSubConstraint = parens "Intersection/Union"
  prettyAnn RecTypeSubConstraint           = parens "muTypeUnfold"


instance PrettyAnn UVarProvenance where
  prettyAnn (RecursiveUVar fv) = parens ("Recursive binding:" <+> prettyAnn fv)
  prettyAnn (ProgramVariable fv) = parens ("Program variable:" <+> prettyAnn fv)
  prettyAnn (PatternMatch loc) = parens ("Return type of pattern match at" <+> prettyAnn loc)
  prettyAnn (DtorAp loc) = parens ("Result type of Dtor application at" <+> prettyAnn loc)
  prettyAnn (TypeSchemeInstance fv loc) = parens ("Instantiation of type scheme" <+> prettyAnn fv <+> "at" <+> prettyAnn loc)


instance PrettyAnn (Constraint ConstraintInfo) where
  prettyAnn (SubType ann t1 t2) =
    prettyAnn t1 <+> "<:" <+> prettyAnn t2 <+> prettyAnn ann

printUVar :: (TVar, UVarProvenance) -> Doc Annotation
printUVar (tv,prov) = prettyAnn tv <+> prettyAnn prov

instance PrettyAnn ConstraintSet where
  prettyAnn ConstraintSet { cs_constraints, cs_uvars } = vsep
    [ "---------------------------------------------------------"
    , "                    ConstraintSet"
    , "---------------------------------------------------------"
    , "Generated unification variables:"
    , nest 3 (line' <> vsep (printUVar <$> cs_uvars))
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

