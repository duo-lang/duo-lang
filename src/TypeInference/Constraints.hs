module TypeInference.Constraints where

import Data.Map (Map)
import qualified Data.Map as M

import Syntax.TST.Types
import Syntax.CST.Names
import Syntax.RST.Types (Polarity(..))
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
  deriving (Show)


data Constraint a where
  SubType :: a -> Typ Pos -> Typ Neg -> Constraint a
  KindEq :: a -> MonoKind -> MonoKind -> Constraint a
  TypeClassPos :: a -> ClassName -> Typ Pos -> Constraint a
  TypeClassNeg :: a -> ClassName -> Typ Neg -> Constraint a
    deriving (Eq, Ord, Functor)

-- | Witnesses generated while solving (sub-)constraints.
-- Provide a path from the subtype to the supertype and thus
-- a coercion function.
data SubtypeWitness
  = SynL RnTypeName SubtypeWitness
  | SynR RnTypeName SubtypeWitness
  | FromTop (Typ Pos)
  | ToBot (Typ Neg)
  | Meet SubtypeWitness SubtypeWitness
  | Join SubtypeWitness SubtypeWitness
  | UnfoldL RecTVar SubtypeWitness
  | UnfoldR RecTVar SubtypeWitness
  | LookupL RecTVar SubtypeWitness
  | LookupR RecTVar SubtypeWitness
  | Data [SubtypeWitness]
  | Codata [SubtypeWitness]
  | DataRefined RnTypeName [SubtypeWitness]
  | CodataRefined RnTypeName [SubtypeWitness]
  | DataNominal RnTypeName [SubtypeWitness]
  | CodataNominal RnTypeName [SubtypeWitness]
  | Refl (Typ Pos) (Typ Neg)
  | SubVar (Constraint ConstraintInfo)
  | Fix (Constraint ())
    -- deriving (Eq, Ord)

-- | Information about the provenance of a unification variable.
data UVarProvenance
  = RecursiveUVar   FreeVarName            -- ^ UVar generated for recursive binding.
  | ProgramVariable FreeVarName            -- ^ UVar generated for program variable.
  | PatternMatch Loc                       -- ^ UVar generated for return type of pattern match.
  | DtorAp Loc                             -- ^ UVar generated for result of Dtor application.
  | TypeSchemeInstance FreeVarName Loc     -- ^ UVar generated for the instantiation of a type scheme.
  | TypeParameter RnTypeName SkolemTVar    -- ^ UVar generated for a type parameter of a nominal type
  | TypeClassInstance ClassName SkolemTVar -- ^ UVar generated for a type parameter of a class instance
  
-- | A ConstraintSet is a set of constraints, together with a list of all the
-- unification variables occurring in them.
data ConstraintSet = ConstraintSet { cs_constraints :: [Constraint ConstraintInfo]
                                   , cs_uvars :: [(UniTVar, UVarProvenance)]
                                   , cs_kvars :: [KVar]
                                   }

------------------------------------------------------------------------------
-- VariableState and SolverResult
------------------------------------------------------------------------------

data VariableState = VariableState
  { vst_upperbounds :: [Typ Neg]
  , vst_lowerbounds :: [Typ Pos]
  , vst_typeclasses :: [ClassName]
  , vst_kind        :: MonoKind
  }

emptyVarState :: MonoKind -> VariableState
emptyVarState = VariableState [] [] []

data SolverResult = MkSolverResult
  { tvarSolution :: Map UniTVar VariableState
  , kvarSolution :: Map KVar MonoKind
    }
