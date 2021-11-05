module TypeInference.Constraints where

import Data.Map (Map)

import Syntax.CommonTerm ( FreeVarName )
import Syntax.Types ( Polarity(..), Typ, TVar )
import Utils ( Loc )


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
  | DtorApConstraint Loc       -- ^ Constraint for checking that destructee of destructor application has correct type.
  | CommandConstraint Loc      -- ^ Constraint was generated from a command `prd >> cns`. (STerms)
  | RecursionConstraint        -- ^ Constraint corresponds to typechecking of recursive function.
  -- Derived constraints generated during constraing solving
  | UpperBoundConstraint
  | LowerBoundConstraint
  | XtorSubConstraint
  | IntersectionUnionSubConstraint
  | RecTypeSubConstraint
  deriving (Show)


data Constraint a = SubType a (Typ Pos) (Typ Neg)
  deriving (Eq, Ord, Functor)

-- | Information about the provenance of a unification variable.
data UVarProvenance
  = RecursiveUVar   FreeVarName        -- ^ UVar generated for recursive binding.
  | ProgramVariable FreeVarName        -- ^ UVar generated for program variable.
  | PatternMatch Loc                   -- ^ UVar generated for return type of pattern match.
  | DtorAp Loc                         -- ^ UVar generated for result of Dtor application.
  | TypeSchemeInstance FreeVarName Loc -- ^ UVar generated for the instantiation of a type scheme.

-- | A ConstraintSet is a set of constraints, together with a list of all the
-- unification variables occurring in them.
data ConstraintSet = ConstraintSet { cs_constraints :: [Constraint ConstraintInfo]
                                   , cs_uvars :: [(TVar, UVarProvenance)]
                                   }

------------------------------------------------------------------------------
-- VariableState and SolverResult
------------------------------------------------------------------------------

data VariableState = VariableState
  { vst_upperbounds :: [Typ Neg]
  , vst_lowerbounds :: [Typ Pos] }

emptyVarState :: VariableState
emptyVarState = VariableState [] []

type SolverResult = Map TVar VariableState