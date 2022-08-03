module Errors where

import Control.Monad.Except
import Data.List.NonEmpty ( NonEmpty )
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text qualified as T

import Syntax.Common
import Syntax.Common.TypesPol
import Utils
import TypeInference.Constraints (ConstraintInfo)

----------------------------------------------------------------------------------
-- Errors emitted during the resolution phase
----------------------------------------------------------------------------------

data ResolutionError where
  -- Type scheme violations
  MissingVarsInTypeScheme :: Loc -> ResolutionError
  -- Polarity violations
  TopInPosPolarity :: Loc -> ResolutionError
  BotInNegPolarity :: Loc -> ResolutionError
  IntersectionInPosPolarity :: Loc -> ResolutionError
  UnionInNegPolarity :: Loc -> ResolutionError
  -- Operator errors
  UnknownOperator :: Loc -> Text -> ResolutionError
  MethodArityMismatch :: Loc
                      -> MethodName
                      -> ClassName
                      -> Int
                      -> Int
                      -> ResolutionError
  XtorArityMismatch :: Loc
                    -> XtorName
                    -> Int
                    -> Int
                    -> ResolutionError
  UndefinedPrimOp :: Loc -> (PrimitiveType, PrimitiveOp) -> ResolutionError
  PrimOpArityMismatch :: Loc
                      -> (PrimitiveType, PrimitiveOp)
                      -> Int
                      -> Int
                      -> ResolutionError
  CmdExpected :: Loc -> Text -> ResolutionError
  InvalidStar  :: Loc -> Text -> ResolutionError

deriving instance Show ResolutionError

instance HasLoc ResolutionError where
  getLoc (MissingVarsInTypeScheme loc) = loc
  getLoc (TopInPosPolarity loc) = loc
  getLoc (BotInNegPolarity loc) = loc
  getLoc (IntersectionInPosPolarity loc) = loc
  getLoc (UnionInNegPolarity loc) = loc
  getLoc (UnknownOperator loc _) = loc
  getLoc (MethodArityMismatch loc _ _ _ _) = loc
  getLoc (XtorArityMismatch loc _ _ _) = loc
  getLoc (UndefinedPrimOp loc _) = loc
  getLoc (PrimOpArityMismatch loc _ _ _) = loc
  getLoc (CmdExpected loc _) = loc
  getLoc (InvalidStar loc _) = loc

instance AttachLoc ResolutionError where
  attachLoc loc (MissingVarsInTypeScheme _) = MissingVarsInTypeScheme loc
  attachLoc loc (TopInPosPolarity _) = TopInPosPolarity loc
  attachLoc loc (BotInNegPolarity _) = BotInNegPolarity loc
  attachLoc loc (IntersectionInPosPolarity _) = IntersectionInPosPolarity loc
  attachLoc loc (UnionInNegPolarity _) = UnionInNegPolarity loc
  attachLoc loc (UnknownOperator _ op) = UnknownOperator loc op
  attachLoc loc (XtorArityMismatch _ xt i1 i2) = XtorArityMismatch loc xt i1 i2
  attachLoc loc (MethodArityMismatch _ mt ct i1 i2) = MethodArityMismatch loc mt ct i1 i2
  attachLoc loc (UndefinedPrimOp _ op) = UndefinedPrimOp loc op
  attachLoc loc (PrimOpArityMismatch _ po i1 i2) = PrimOpArityMismatch loc po i1 i2
  attachLoc loc (CmdExpected _ t) = CmdExpected loc t
  attachLoc loc (InvalidStar _ t) = InvalidStar loc t

----------------------------------------------------------------------------------
-- Errors emitted during the constraint generation phase
----------------------------------------------------------------------------------

data ConstraintGenerationError where
  -- | A bound variable is not bound in the context. (Likely implementation error).
  BoundVariableOutOfBounds :: Loc -> PrdCns -> Index -> ConstraintGenerationError
  -- | A bound variable is used with the wrong mode (Prd/Cns).
  BoundVariableWrongMode :: Loc -> PrdCns -> Index -> ConstraintGenerationError
  -- | A pattern match fails to match on given constructor/destructor.
  PatternMatchMissingXtor :: Loc -> XtorName -> RnTypeName -> ConstraintGenerationError
  -- | A pattern match tries to match on a constructor/destructor not contained in declaration.
  PatternMatchAdditional :: Loc -> XtorName -> RnTypeName -> ConstraintGenerationError
  -- | Typeclass method contained in class declaration, but missing in instance implementation.
  InstanceImplementationMissing :: Loc -> MethodName -> ConstraintGenerationError
  -- | Typeclass method implemented in instance, but not contained in class declaration.
  InstanceImplementationAdditional :: Loc -> MethodName -> ConstraintGenerationError
  -- | Could not find signature for given primitive operation.
  PrimitiveOpMissingSignature :: Loc -> PrimitiveOp -> PrimitiveType -> ConstraintGenerationError
  -- | One cannot infer a type for an empty nominal match.
  EmptyNominalMatch :: Loc -> ConstraintGenerationError
  -- | One cannot infer a type for an empty refinement match.
  EmptyRefinementMatch :: Loc -> ConstraintGenerationError
  -- | Linear contexts have unequal length.
  LinearContextsUnequalLength :: Loc -> ConstraintInfo -> LinearContext Pos -> LinearContext Neg -> ConstraintGenerationError
  LinearContextIncompatibleTypeMode :: Loc -> PrdCns -> ConstraintInfo -> ConstraintGenerationError
  ExpectedRefinementFoundNominal :: Loc -> XtorName -> ConstraintGenerationError


deriving instance Show ConstraintGenerationError

instance HasLoc ConstraintGenerationError where
  getLoc (BoundVariableOutOfBounds loc _ _) = loc
  getLoc (BoundVariableWrongMode loc _ _) = loc
  getLoc (PatternMatchMissingXtor loc _ _) = loc
  getLoc (PatternMatchAdditional loc _ _) = loc
  getLoc (InstanceImplementationMissing loc _) = loc
  getLoc (InstanceImplementationAdditional loc _) = loc
  getLoc (PrimitiveOpMissingSignature loc _ _) = loc
  getLoc (EmptyNominalMatch loc) = loc
  getLoc (EmptyRefinementMatch loc) = loc
  getLoc (LinearContextsUnequalLength loc _ _ _) = loc
  getLoc (LinearContextIncompatibleTypeMode loc _ _) = loc
  getLoc (ExpectedRefinementFoundNominal loc _) = loc

instance AttachLoc ConstraintGenerationError where
  attachLoc loc (BoundVariableOutOfBounds _ pc idx) = BoundVariableOutOfBounds loc pc idx
  attachLoc loc (BoundVariableWrongMode _ pc idx) = BoundVariableWrongMode loc pc idx
  attachLoc loc (PatternMatchMissingXtor _ xn tn)  = PatternMatchMissingXtor loc xn tn
  attachLoc loc (PatternMatchAdditional _ xn tn) = PatternMatchAdditional loc xn tn
  attachLoc loc (InstanceImplementationMissing _ mn) = InstanceImplementationMissing loc mn
  attachLoc loc (InstanceImplementationAdditional _ mn) = InstanceImplementationAdditional loc mn
  attachLoc loc (PrimitiveOpMissingSignature _ po pt) = PrimitiveOpMissingSignature loc po pt
  attachLoc loc (EmptyNominalMatch _) = EmptyNominalMatch loc
  attachLoc loc (EmptyRefinementMatch _) = EmptyRefinementMatch loc
  attachLoc loc (LinearContextsUnequalLength _ ci ctx1 ctx2) = LinearContextsUnequalLength loc ci ctx1 ctx2
  attachLoc loc (LinearContextIncompatibleTypeMode _ pc ci) = LinearContextIncompatibleTypeMode loc pc ci
  attachLoc loc (ExpectedRefinementFoundNominal _ tn) = ExpectedRefinementFoundNominal loc tn


----------------------------------------------------------------------------------
-- Errors emitted during the constraint solving phase
----------------------------------------------------------------------------------

data ConstraintSolverError where
  SomeConstraintSolverError :: Loc -> Text -> ConstraintSolverError

deriving instance Show ConstraintSolverError

instance HasLoc ConstraintSolverError where
  getLoc (SomeConstraintSolverError loc _) =
    loc

instance AttachLoc ConstraintSolverError where
  attachLoc loc (SomeConstraintSolverError _ msg) =
    SomeConstraintSolverError loc msg

----------------------------------------------------------------------------------
-- Errors emitted during the type simplification phase
----------------------------------------------------------------------------------

data TypeAutomatonError where
  SomeTypeAutomatonError :: Loc -> Text -> TypeAutomatonError

deriving instance Show TypeAutomatonError

instance HasLoc TypeAutomatonError where
  getLoc (SomeTypeAutomatonError loc _) =
    loc

instance AttachLoc TypeAutomatonError where
  attachLoc loc (SomeTypeAutomatonError _ msg) =
    SomeTypeAutomatonError loc msg

----------------------------------------------------------------------------------
-- Errors emitted during evaluation
----------------------------------------------------------------------------------

data EvalError where
  SomeEvalError :: Loc -> Text -> EvalError

deriving instance Show EvalError

instance HasLoc EvalError where
  getLoc (SomeEvalError loc _) =
    loc

instance AttachLoc EvalError where
  attachLoc loc (SomeEvalError _ msg) =
    SomeEvalError loc msg

----------------------------------------------------------------------------------
-- Errors emitted during parsing
----------------------------------------------------------------------------------

data ParserError where
  SomeParserError :: Loc -> Text -> ParserError

deriving instance Show ParserError

instance HasLoc ParserError where
  getLoc (SomeParserError loc _) =
    loc

instance AttachLoc ParserError where
  attachLoc loc (SomeParserError _ msg) =
    SomeParserError loc msg

----------------------------------------------------------------------------------
-- Various other errors
----------------------------------------------------------------------------------

data OtherError where
  SomeOtherError :: Loc -> Text -> OtherError

deriving instance Show OtherError

instance HasLoc OtherError where
  getLoc (SomeOtherError loc _) =
    loc

instance AttachLoc OtherError where
  attachLoc loc (SomeOtherError _ msg) =
    SomeOtherError loc msg

----------------------------------------------------------------------------------
-- Errors
----------------------------------------------------------------------------------

data Error where
  ErrConstraintGeneration :: ConstraintGenerationError -> Error
  ErrResolution           :: ResolutionError           -> Error
  ErrConstraintSolver     :: ConstraintSolverError     -> Error
  ErrTypeAutomaton        :: TypeAutomatonError        -> Error
  ErrEval                 :: EvalError                 -> Error
  ErrOther                :: OtherError                -> Error
  ErrParser               :: ParserError               -> Error
  deriving (Show)

instance HasLoc Error where
  getLoc (ErrConstraintGeneration err) = getLoc err
  getLoc (ErrResolution err)           = getLoc err
  getLoc (ErrConstraintSolver err)     = getLoc err
  getLoc (ErrTypeAutomaton err)        = getLoc err
  getLoc (ErrEval err)                 = getLoc err
  getLoc (ErrOther err)                = getLoc err
  getLoc (ErrParser err)               = getLoc err

instance AttachLoc Error where
  attachLoc loc (ErrConstraintGeneration err) = ErrConstraintGeneration (attachLoc loc err)
  attachLoc loc (ErrResolution err)           = ErrResolution (attachLoc loc err)
  attachLoc loc (ErrConstraintSolver err)     = ErrConstraintSolver (attachLoc loc err)
  attachLoc loc (ErrTypeAutomaton err)        = ErrTypeAutomaton (attachLoc loc err)
  attachLoc loc (ErrEval err)                 = ErrEval (attachLoc loc err)
  attachLoc loc (ErrOther err)                = ErrOther (attachLoc loc err)
  attachLoc loc (ErrParser err)               = ErrParser (attachLoc loc err)

---------------------------------------------------------------------------------------------
-- Throwing errors in a monadic context
---------------------------------------------------------------------------------------------

throwGenError :: MonadError (NonEmpty Error) m
              => ConstraintGenerationError -> m a
throwGenError  =
  throwError . (NE.:| []) . ErrConstraintGeneration

throwEvalError :: MonadError (NonEmpty Error) m
               => Loc -> [Text] -> m a
throwEvalError loc =
  throwError . (NE.:| []) . (ErrEval . SomeEvalError loc) . T.unlines

throwSolverError :: MonadError (NonEmpty Error) m
                 => Loc -> [Text] -> m a
throwSolverError loc =
  throwError . (NE.:| []) . (ErrConstraintSolver . SomeConstraintSolverError loc) . T.unlines

throwAutomatonError :: MonadError (NonEmpty Error) m
                    => Loc -> [Text] -> m a
throwAutomatonError loc =
  throwError . (NE.:| []) . (ErrTypeAutomaton . SomeTypeAutomatonError loc) . T.unlines

throwOtherError :: MonadError (NonEmpty Error) m
                => Loc -> [Text] -> m a
throwOtherError loc =
  throwError . (NE.:| []) . (ErrOther . SomeOtherError loc) . T.unlines


---------------------------------------------------------------------------------------------
-- Warnings
---------------------------------------------------------------------------------------------

data Warning where
  -- | Warning for producer that starts with the letter "k".
  MisnamedProducerVar :: Loc -> Text -> Warning
  -- | Warning for consumer that doesn't start with the letter "k".
  MisnamedConsumerVar :: Loc -> Text -> Warning

deriving instance Show Warning

instance HasLoc Warning where
  getLoc (MisnamedProducerVar loc _) = loc
  getLoc (MisnamedConsumerVar loc _) = loc

instance AttachLoc Warning where
  attachLoc loc (MisnamedProducerVar _ msg) = MisnamedProducerVar loc msg
  attachLoc loc (MisnamedConsumerVar _ msg) = MisnamedConsumerVar loc msg
