module TypeInference.Constraints where

import Data.Map (Map)

import Syntax.TST.Types
import Syntax.CST.Names
import Syntax.RST.Types (Polarity(..))
import Syntax.RST.Names
import Syntax.CST.Kinds
import Loc ( Loc )


------------------------------------------------------------------------------
-- Constraints
------------------------------------------------------------------------------

-- | Information about the provenance of a constraint.
data ConstraintInfo
  -- Primitive constraints from constraint generation:
  = CtorArgsConstraint Loc     -- ^ Constraint for checking that args of constructor call have correct type.
  | DtorArgsConstraint Loc     -- ^ Constraint for checking that args of destructor call have correct type.
  | CaseConstraint Loc         -- ^ Constraint for checking that a pattern-match case has correct return type.
  | PatternMatchConstraint Loc -- ^ Constraint for checking that destructee of pattern match has correct type.
  | InstanceConstraint Loc     -- ^ Constraint for checking that type matches the type specified in the instance declaration.
  | DtorApConstraint Loc       -- ^ Constraint for checking that destructee of destructor application has correct type.
  | CommandConstraint Loc      -- ^ Constraint was generated from a command `prd >> cns`.
  | ReadConstraint Loc         -- ^ Constraint was generated from a `Read[cns]` command
  | RecursionConstraint        -- ^ Constraint corresponds to typechecking of recursive function.
  | PrimOpArgsConstraint Loc   -- ^ Constraint for checking that args of primitive operation have correct type
  | TypeClassConstraint Loc    -- ^ Constraint for checking that type class instance for type exists.
  -- Derived constraints generated during constraing solving
  | UpperBoundConstraint
  | LowerBoundConstraint
  | XtorSubConstraint
  | IntersectionUnionSubConstraint
  | RecTypeSubConstraint
  | NominalSubConstraint
  | KindConstraint
  | ClassResolutionConstraint
  deriving (Show)


data Constraint a where
  SubType :: a -> Typ Pos -> Typ Neg -> Constraint a
  KindEq :: a -> AnyKind -> AnyKind -> Constraint a
  TypeClass :: a -> ClassName -> UniTVar -> Constraint a
    deriving (Eq, Ord, Functor)

-- | Witnesses generated while solving (sub-)constraints.
-- Provide a path from the subtype to the supertype and thus
-- a coercion function.
data SubtypeWitness
  = SynL RnTypeName SubtypeWitness
  -- ^ Witness for type synonym as subtype with substituted subconstraint.
  | SynR RnTypeName SubtypeWitness
  -- ^ Witness for type synonym as supertype with substituted subconstraint.
  | FromTop (Typ Pos)
  -- ^ Witness for the type being a subtype of /Top/.
  | ToBot (Typ Neg)
  -- ^ Witness for the type being a supertype of /Bot/.
  | Inter SubtypeWitness SubtypeWitness
  -- ^ Witness for a type being a subtype on an intersection type, therefore having to be a subtype of both.
  | Union SubtypeWitness SubtypeWitness
  -- ^ Witness for a type being a supertype on a union type, therefore having to be a supertype of both.
  | UnfoldL RecTVar SubtypeWitness
  -- ^ Witness for a recursive subtype with its unfolded representation as a subwitness.
  | UnfoldR RecTVar SubtypeWitness
  -- ^ Witness for a recursive supertype with its unfolded representation as a subwitness.
  | Data [SubtypeWitness]
  -- ^ Witness for two data types and subwitnesses for each constructor.
  | Codata [SubtypeWitness]
  -- ^ Witness for two codata types and subwitnesses for each destructor.
  | DataRefined RnTypeName [SubtypeWitness]
  -- ^ Witness for two refined data types and subwitnesses for each constructor.
  | CodataRefined RnTypeName [SubtypeWitness]
  -- ^ Witness for two refined codata types and subwitnesses for each destructor.
  | DataNominal RnTypeName [SubtypeWitness]
  -- ^ Witness for two nominal (co-)data types and subwitnesses for their arguments.
  | Refl (Typ Pos) (Typ Neg)
  -- ^ Witness for the reflexivity of the subtyping relation. Contains a positive and negative representation of the same type.
  | UVarL UniTVar (Typ Neg)
  -- ^ Witness that a type is an upper bound of a unification variable.
  | UVarR UniTVar (Typ Pos)
  -- ^ Witness that a type is a lower bound of a unification variable.
  | SubVar (Constraint ())
  -- ^ Witness "hole" containing a constraint which should be substituted by its witness. Only used when generating subwitnesses.
  | Fix (Constraint ())
  -- ^ Pointer to a previously solved constraint so that witnesses for recursive types are finite.
    deriving (Eq, Ord)

-- | Information about the provenance of a unification variable.
data UVarProvenance
  = RecursiveUVar   FreeVarName            -- ^ UVar generated for recursive binding.
  | ProgramVariable FreeVarName            -- ^ UVar generated for program variable.
  | PatternMatch Loc                       -- ^ UVar generated for return type of pattern match.
  | DtorAp Loc                             -- ^ UVar generated for result of Dtor application.
  | TypeSchemeInstance FreeVarName Loc     -- ^ UVar generated for the instantiation of a type scheme.
  | TypeParameter RnTypeName SkolemTVar    -- ^ UVar generated for a type parameter of a nominal type
  | TypeClassInstance ClassName SkolemTVar -- ^ UVar generated for a type parameter of a class instance
  | TypeClassResolution                    -- ^ Placeholder UVar generated during type class resolution.
  
-- | A ConstraintSet is a set of constraints, together with a list of all the
-- unification variables occurring in them.
data ConstraintSet = ConstraintSet { cs_constraints :: [Constraint ConstraintInfo]
                                   , cs_uvars :: [(UniTVar, UVarProvenance, AnyKind)]
                                   , cs_kvars :: [KVar]
                                   }

------------------------------------------------------------------------------
-- VariableState and SolverResult
------------------------------------------------------------------------------

data VariableState = VariableState
  { vst_upperbounds :: [Typ Neg]
  , vst_lowerbounds :: [Typ Pos]
  , vst_typeclasses :: [ClassName]
  , vst_kind        :: AnyKind
  }

emptyVarState :: AnyKind -> VariableState
emptyVarState = VariableState [] [] []

data SolverResult = MkSolverResult
  { tvarSolution     :: Map UniTVar VariableState
  , kvarSolution   :: Map KVar AnyKind
  , witnessSolution  :: Map (Constraint ()) SubtypeWitness
  }

newtype InstanceResult = MkInstanceResult
  { instanceResult :: Map (UniTVar, ClassName) (FreeVarName, Typ Pos, Typ Neg) }
