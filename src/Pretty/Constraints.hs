module Pretty.Constraints () where

import Prettyprinter
import Data.List (intersperse)
import Data.Map qualified as M

import Pretty.Pretty
import Pretty.Types ()
import Syntax.Common.TypesPol
import Syntax.Common
import TypeInference.Constraints

---------------------------------------------------------------------------------
-- Generated Constraints
---------------------------------------------------------------------------------

instance PrettyAnn ConstraintInfo where
  -- Primary Constraints
  prettyAnn (CtorArgsConstraint loc) = parens ("Ctor args constraint at" <+> prettyAnn loc)
  prettyAnn (DtorArgsConstraint loc) = parens ("Dtor args constraint at" <+> prettyAnn loc)
  prettyAnn (CaseConstraint loc) = parens ("Case constraint at" <+> prettyAnn loc)
  prettyAnn (PatternMatchConstraint loc) = parens ("Pattern match constraint at" <+> prettyAnn loc)
  prettyAnn (DtorApConstraint loc) = parens ("DtorAp constraint at" <+> prettyAnn loc)
  prettyAnn (CommandConstraint loc) = parens ("Constraint from logical command at" <+> prettyAnn loc)
  prettyAnn (ReadConstraint loc)    = parens ("Constraint from Read command at" <+> prettyAnn loc)
  prettyAnn RecursionConstraint = parens "Recursive"
  prettyAnn (PrimOpArgsConstraint loc)     = parens ("Primitive operation args constraint at" <+> prettyAnn loc)
  -- Derived Constraints
  prettyAnn UpperBoundConstraint           = parens "UpperBound"
  prettyAnn LowerBoundConstraint           = parens "LowerBound"
  prettyAnn XtorSubConstraint              = parens "XtorSubConstraint"
  prettyAnn IntersectionUnionSubConstraint = parens "Intersection/Union"
  prettyAnn RecTypeSubConstraint           = parens "muTypeUnfold"
  prettyAnn NominalSubConstraint           = parens "NominalSubConstraint"

instance PrettyAnn UVarProvenance where
  prettyAnn (RecursiveUVar fv) = parens ("Recursive binding:" <+> prettyAnn fv)
  prettyAnn (ProgramVariable fv) = parens ("Program variable:" <+> prettyAnn fv)
  prettyAnn (PatternMatch loc) = parens ("Return type of pattern match at" <+> prettyAnn loc)
  prettyAnn (DtorAp loc) = parens ("Result type of Dtor application at" <+> prettyAnn loc)
  prettyAnn (TypeSchemeInstance fv loc) = parens ("Instantiation of type scheme" <+> prettyAnn fv <+> "at" <+> prettyAnn loc)
  prettyAnn (TypeParameter tn tv) = parens ("Instantiation of type parameter" <+> prettyAnn tv <+> "for" <+> prettyAnn tn)

instance PrettyAnn (Constraint ConstraintInfo) where
  prettyAnn (SubType ann t1 t2) =
    prettyAnn t1 <+> "<:" <+> prettyAnn t2 <+> prettyAnn ann

printUVar :: (TUniVar, UVarProvenance) -> Doc Annotation
printUVar (tv,prov) = prettyAnn tv <+> prettyAnn prov

instance PrettyAnn ConstraintSet where
  prettyAnn ConstraintSet { cs_constraints, cs_uvars } = vsep
    [ "---------------------------------------------------------"
    , "                    Generated Constraints"
    , "---------------------------------------------------------"
    , ""
    , "Generated unification variables:"
    , nest 3 (line' <> vsep (printUVar <$> cs_uvars))
    , ""
    , "Generated constraints:"
    , nest 3 (line' <> vsep (prettyAnn <$> cs_constraints))
    , ""
    ]

---------------------------------------------------------------------------------
-- Solved Constraints
---------------------------------------------------------------------------------

printLowerBounds :: [Typ 'Pos] -> Doc Annotation
printLowerBounds [] = mempty
printLowerBounds lowerbounds =
  nest 3 $ vsep [ "Lower bounds:"
                ,  vsep (prettyAnn <$> lowerbounds)
                ]

printUpperBounds :: [Typ 'Neg] -> Doc Annotation
printUpperBounds [] = mempty
printUpperBounds upperbounds =
  nest 3 $ vsep [ "Upper bounds:"
                , vsep (prettyAnn <$> upperbounds)
                ]

instance PrettyAnn VariableState where
  prettyAnn VariableState { vst_lowerbounds = []  , vst_upperbounds = []  } = mempty
  prettyAnn VariableState { vst_lowerbounds = lbs , vst_upperbounds = []  } = printLowerBounds lbs
  prettyAnn VariableState { vst_lowerbounds = []  , vst_upperbounds = ubs } = printUpperBounds ubs
  prettyAnn VariableState { vst_lowerbounds = lbs , vst_upperbounds = ubs } =
    printLowerBounds lbs <> line <> printUpperBounds ubs

instance PrettyAnn SolverResult where
  prettyAnn MkSolverResult { tvarSolution } = vsep
    [ "---------------------------------------------------------"
    , "                   Solved Constraints"
    , "---------------------------------------------------------"
    , ""
    , vsep $ intersperse "" (solvedConstraintsToDoc <$> M.toList tvarSolution)
    , ""
    ]
    where
      solvedConstraintsToDoc :: (TUniVar,VariableState) -> Doc Annotation
      solvedConstraintsToDoc (v, vs) = nest 3 $ vsep ["Type variable:" <+> prettyAnn v
                                                     , prettyAnn vs
                                                     ]


---------------------------------------------------------------------------------
-- Bisubstitutions
---------------------------------------------------------------------------------

prettyBisubst :: (TUniVar, (Typ 'Pos, Typ 'Neg)) -> Doc Annotation
prettyBisubst (v, (typ,tyn)) = nest 3 $ vsep ["Type variable:" <+> prettyAnn v
                                             , vsep [ "+ |->" <+> prettyAnn typ
                                                    , "- |->" <+> prettyAnn tyn
                                                    ]
                                             ]

instance PrettyAnn Bisubstitution where
  prettyAnn (MkBisubstitution uvsubst) = vsep
    [ "---------------------------------------------------------"
    , "                 Bisubstitution                          "
    , "---------------------------------------------------------"
    , ""
    , vsep $ intersperse "" (prettyBisubst <$> M.toList uvsubst)
    , "---------------------------------------------------------"
    ]
