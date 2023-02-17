module Pretty.Constraints () where

import Prettyprinter
import Data.List (intersperse)
import Data.Map qualified as M

import Pretty.Pretty
import Pretty.Types ()
import Syntax.TST.Types qualified as TST
import Syntax.RST.Types (Polarity(..), PolarityRep (..))
import Syntax.CST.Names
import TypeInference.Constraints
import Syntax.CST.Kinds

---------------------------------------------------------------------------------
-- Generated Constraints
---------------------------------------------------------------------------------

instance PrettyAnn ConstraintInfo where
  -- Primary Constraints
  prettyAnn (CtorArgsConstraint loc) = parens ("Ctor args constraint at" <+> prettyAnn loc)
  prettyAnn (DtorArgsConstraint loc) = parens ("Dtor args constraint at" <+> prettyAnn loc)
  prettyAnn (CaseConstraint loc) = parens ("Case constraint at" <+> prettyAnn loc)
  prettyAnn (PatternMatchConstraint loc) = parens ("Pattern match constraint at" <+> prettyAnn loc)
  prettyAnn (InstanceConstraint loc) = parens ("Instance constraint at" <+> prettyAnn loc)
  prettyAnn (DtorApConstraint loc) = parens ("DtorAp constraint at" <+> prettyAnn loc)
  prettyAnn (CommandConstraint loc) = parens ("Constraint from logical command at" <+> prettyAnn loc)
  prettyAnn (ReadConstraint loc)    = parens ("Constraint from Read command at" <+> prettyAnn loc)
  prettyAnn RecursionConstraint = parens "Recursive"
  prettyAnn (PrimOpArgsConstraint loc)     = parens ("Primitive operation args constraint at" <+> prettyAnn loc)
  prettyAnn (TypeClassConstraint loc) = parens ("Type class constraint at" <+> prettyAnn loc)
  prettyAnn KindConstraint = parens "Kind Constraint"
  -- Derived Constraints
  prettyAnn UpperBoundConstraint           = parens "UpperBound"
  prettyAnn LowerBoundConstraint           = parens "LowerBound"
  prettyAnn XtorSubConstraint              = parens "XtorSubConstraint"
  prettyAnn IntersectionUnionSubConstraint = parens "Intersection/Union"
  prettyAnn RecTypeSubConstraint           = parens "muTypeUnfold"
  prettyAnn NominalSubConstraint           = parens "NominalSubConstraint"
  prettyAnn ApplicationSubConstraint       = parens "ApplicationSubConstraint"
  prettyAnn RefinementSubConstraint        = parens "RefinementSubConstraint"
  prettyAnn ClassResolutionConstraint      = parens "ClassResolutionConstraint"


instance PrettyAnn UVarProvenance where
  prettyAnn (RecursiveUVar fv) = parens ("Recursive binding:" <+> prettyAnn fv)
  prettyAnn (ProgramVariable fv) = parens ("Program variable:" <+> prettyAnn fv)
  prettyAnn (PatternMatch loc) = parens ("Return type of pattern match at" <+> prettyAnn loc)
  prettyAnn (DtorAp loc) = parens ("Result type of Dtor application at" <+> prettyAnn loc)
  prettyAnn (TypeSchemeInstance fv loc) = parens ("Instantiation of type scheme" <+> prettyAnn fv <+> "at" <+> prettyAnn loc)
  prettyAnn (TypeParameter tn tv) = parens ("Instantiation of type parameter" <+> prettyAnn tv <+> "for" <+> prettyAnn tn)
  prettyAnn (TypeClassInstance cn tv) = parens ("Instantiation for type variable"  <+> prettyAnn tv <+> "of type class" <+> prettyAnn cn)
  prettyAnn TypeClassResolution = "TypeClassResolution placeholder"

instance (PrettyAnn a) => PrettyAnn (Constraint a) where
  prettyAnn (KindEq ann k1 k2) =
    prettyAnn k1 <+> "~" <+> prettyAnn k2 <+> prettyAnn ann
  prettyAnn (SubType ann t1 t2) =
    prettyAnn t1 <+> "<:" <+> prettyAnn t2 <+> prettyAnn ann
  prettyAnn (TypeClass ann cn typ) =
    prettyAnn cn <+> prettyAnn typ <+> prettyAnn ann

printUVar :: (UniTVar, UVarProvenance, AnyKind) -> Doc Annotation
printUVar (tv,prov,kv) = prettyAnn tv <> ":" <> prettyAnn kv <+> prettyAnn prov

instance PrettyAnn ConstraintSet where
  prettyAnn cs = vsep
    [ headerise "-" " " "Generated Constraints"
    , ""
    , "Generated unification variables:"
    , nest 3 (line' <> vsep (printUVar <$> cs.cs_uvars))
    , ""
    , "Generated Kind Variables: "
    , nest 3 (line' <> vsep (prettyAnn <$> cs.cs_kvars))
    , ""
    , "Generated constraints:"
    , nest 3 (line' <> vsep (prettyAnn <$> cs.cs_constraints))
    , ""
    ]

---------------------------------------------------------------------------------
-- Witnesses
---------------------------------------------------------------------------------

instance PrettyAnn SubtypeWitness where
  prettyAnn (SynL rn w) = "SynL" <> brackets (prettyAnn rn) <> parens (prettyAnn w)
  prettyAnn (SynR rn w) = "SynR" <> brackets (prettyAnn rn) <> parens (prettyAnn w)
  prettyAnn (FromTop typ) = "FromTop" <> brackets (prettyAnn typ)
  prettyAnn (ToBot tyn) = "ToBot" <> brackets (prettyAnn tyn)
  prettyAnn (Inter w1 w2) = "Inter" <> parens (sep $ intersperse "," $ prettyAnn <$> [w1, w2])
  prettyAnn (Union w1 w2) = "Union" <> parens (sep $ intersperse "," $ prettyAnn <$> [w1, w2])
  prettyAnn (UnfoldL recTVar w) = "UnfoldL" <> brackets (prettyAnn recTVar) <> parens (prettyAnn w)
  prettyAnn (UnfoldR recTVar w) = "UnfoldR" <> brackets (prettyAnn recTVar) <> parens (prettyAnn w)
  prettyAnn (Data ws) = "Data" <> parens (sep $ intersperse "," $ prettyAnn <$> ws)
  prettyAnn (Codata ws) = "Codata" <> parens (sep $ intersperse "," $ prettyAnn <$> ws)
  prettyAnn (DataRefined rn ws) = "DataRefined" <> brackets (prettyAnn rn) <> parens (sep $ intersperse "," $ prettyAnn <$> ws)
  prettyAnn (CodataRefined rn ws) = "CodataRefined" <> brackets (prettyAnn rn) <> parens (sep $ intersperse "," $ prettyAnn <$> ws)
  prettyAnn (DataNominal rn ws) = "DataNominal" <> brackets (prettyAnn rn) <> parens (sep $ intersperse "," $ prettyAnn <$> ws)
  prettyAnn (DataApp typ tyn ws) = "DataApp" <> brackets (prettyAnn typ) <> parens (prettyAnn tyn) <> parens (sep $ intersperse "," $ prettyAnn <$> ws)
  prettyAnn (Refl typ _tyn) = "Refl" <> brackets (prettyAnn typ)
  prettyAnn (UVarL uv tyn) = "UVarL" <> brackets (prettyAnn uv) <> parens (prettyAnn tyn)
  prettyAnn (UVarR uv typ) = "UVarR" <> brackets (prettyAnn uv) <> parens (prettyAnn typ)
  prettyAnn (SubVar cs) = "SubVar" <> braces (prettyAnn cs)
  prettyAnn (Fix cs) = "Fix" <> braces (prettyAnn cs)

---------------------------------------------------------------------------------
-- Solved Constraints
---------------------------------------------------------------------------------

printBounds :: PolarityRep pc -> UniTVar -> [TST.Typ pc] -> Doc Annotation
printBounds _ _ [] = mempty
printBounds pc u bounds = prettyAnn u <+> (case pc of PosRep -> "lower bounds:"; NegRep -> "upper bounds:") <> mkParen True mempty mempty comma (prettyAnn <$> bounds)


printTypeClassConstraints :: UniTVar -> [ClassName] -> Doc Annotation
printTypeClassConstraints _ [] = mempty
printTypeClassConstraints u cns = prettyAnn u <+> "type class constraints:" <>  mkParen True mempty mempty comma (prettyAnn <$> cns)


prettyVariableState :: (UniTVar, VariableState) -> Doc Annotation
prettyVariableState (_, VariableState { vst_lowerbounds = []  , vst_upperbounds = []  , vst_typeclasses = []  }) =
    mempty
prettyVariableState (u, VariableState { vst_lowerbounds = []  , vst_upperbounds = []  , vst_typeclasses = cns }) =
    printTypeClassConstraints u cns
prettyVariableState (u, VariableState { vst_lowerbounds = lbs , vst_upperbounds = []  , vst_typeclasses = []  }) =
    printBounds PosRep u lbs
prettyVariableState (u, VariableState { vst_lowerbounds = lbs , vst_upperbounds = []  , vst_typeclasses = cns }) =
    printBounds PosRep u lbs <> line <> printTypeClassConstraints u cns
prettyVariableState (u, VariableState { vst_lowerbounds = []  , vst_upperbounds = ubs , vst_typeclasses = []  }) =
    printBounds NegRep u ubs
prettyVariableState (u, VariableState { vst_lowerbounds = []  , vst_upperbounds = ubs , vst_typeclasses = cns }) =
    printBounds NegRep u ubs <> line <> printTypeClassConstraints u cns
prettyVariableState (u, VariableState { vst_lowerbounds = lbs , vst_upperbounds = ubs , vst_typeclasses = []  }) =
    printBounds PosRep u lbs <> line <> printBounds NegRep u ubs
prettyVariableState (u, VariableState { vst_lowerbounds = lbs , vst_upperbounds = ubs , vst_typeclasses = cns }) =
    printBounds PosRep u lbs <> line <> printBounds NegRep u ubs <> line <> printTypeClassConstraints u cns

instance PrettyAnn SolverResult where
  prettyAnn result = vsep

    [ headerise "-" " " "Solved Constraints"
    , ""
    , vsep $ intersperse "" (prettyVariableState <$> M.toList result.tvarSolution)
    , ""
    , headerise "-" " " "Generated Witnesses:"
    , ""
    , vsep $ intersperse "" (solvedWitnessesToDoc <$> M.toList result.witnessSolution)
    , ""
    ]
    where
      solvedWitnessesToDoc :: (Constraint (), SubtypeWitness) -> Doc Annotation
      solvedWitnessesToDoc (cs, w) = nest 3 $ vsep ["Constraint:" <+> prettyAnn cs
                                                   , prettyAnn w
                                                   ]


---------------------------------------------------------------------------------
-- Bisubstitutions
---------------------------------------------------------------------------------

prettyBisubst :: (UniTVar, (TST.Typ 'Pos, TST.Typ 'Neg)) -> Doc Annotation
prettyBisubst (v, (typ,tyn)) = nest 3 $ line <> vsep [ prettyAnn v <+> "+ ⤇" <+> prettyAnn typ
                                                     , prettyAnn v <+> "- ⤇" <+> prettyAnn tyn
                                                     ]

prettyRecBisubst :: (RecTVar, (TST.Typ 'Pos, TST.Typ 'Neg)) -> Doc Annotation
prettyRecBisubst (v, (typ,tyn)) = nest 3 $ line <> vsep [ prettyAnn v <+> "+ ⤇" <+> prettyAnn typ
                                                        , prettyAnn v <+> "- ⤇" <+> prettyAnn tyn
                                                        ]

prettySkolBisubst :: (SkolemTVar, (TST.Typ 'Pos, TST.Typ 'Neg)) -> Doc Annotation
prettySkolBisubst (v, (typ,tyn)) = nest 3 $ line <> vsep [ prettyAnn v <+> "+ ⤇" <+> prettyAnn typ
                                                         , prettyAnn v <+> "- ⤇" <+> prettyAnn tyn
                                                         ]

prettyKindSubst :: (KVar, AnyKind) -> Doc Annotation
prettyKindSubst (kv, kind) = nest 3 $ vsep ["Kind Variable:" <+> prettyAnn kv <+> "->" <+> prettyAnn kind ]

instance PrettyAnn (TST.Bisubstitution TST.UniVT) where
  prettyAnn uvsubst = vsep
    [ headerise "-" " " "Bisubstitution (UniTVar)"
    , ""
    , "Unification Variables: "
    , vsep $ prettyBisubst <$> M.toList (fst uvsubst.bisubst_map)
    , ""
    , "Kind Variables: "
    , vsep $ intersperse "" (prettyKindSubst <$> M.toList (snd uvsubst.bisubst_map))
    ]

instance PrettyAnn (TST.Bisubstitution TST.SkolemVT) where
  prettyAnn skolvsubst = vsep
    [ headerise "-" " " "Bisubstitution (SkolemTVar)"
    , ""
    , vsep $ prettySkolBisubst <$> M.toList skolvsubst.bisubst_map
    ]

instance PrettyAnn (TST.Bisubstitution TST.RecVT) where
  prettyAnn recvsubst = vsep
    [ headerise "-" " " "Bisubstitution (RecTVar)"
    , ""
    , vsep $ prettyRecBisubst <$> M.toList recvsubst.bisubst_map 
    ]


---------------------------------------------------------------------------------
-- Instance resolution
---------------------------------------------------------------------------------

prettyInstanceRes :: (UniTVar, ClassName) -> (FreeVarName, TST.Typ Pos, TST.Typ Neg) -> Doc Annotation
prettyInstanceRes (uv, cn) (iname, typ, _tyn) = prettyAnn cn <+> prettyAnn uv <+> "~>"
                                            <+> prettyAnn iname <+> ":" <+> prettyAnn cn <+> prettyAnn typ

instance PrettyAnn InstanceResult where
  prettyAnn (MkInstanceResult instanceRes) =
    let instances = M.toList instanceRes
    in case instances of
      [] -> mempty
      _  -> vsep
              [ headerise "-" " " "Resolved Instances"
              , ""
              , vsep $ uncurry prettyInstanceRes <$> instances
              ]
