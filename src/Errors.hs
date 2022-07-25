module Errors where

import Control.Monad.Except
import Data.List.NonEmpty ( NonEmpty )
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text qualified as T

import Syntax.Common
import Utils

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
  attachLoc loc (UndefinedPrimOp _ op) = UndefinedPrimOp loc op
  attachLoc loc (PrimOpArityMismatch _ po i1 i2) = PrimOpArityMismatch loc po i1 i2
  attachLoc loc (CmdExpected _ t) = CmdExpected loc t
  attachLoc loc (InvalidStar _ t) = InvalidStar loc t

----------------------------------------------------------------------------------
-- Errors emitted during the constraint generation phase
----------------------------------------------------------------------------------

data ConstraintGenerationError where
  SomeConstraintGenerationError :: Loc -> Text -> ConstraintGenerationError

deriving instance Show ConstraintGenerationError

instance HasLoc ConstraintGenerationError where
  getLoc (SomeConstraintGenerationError loc _) =
    loc

instance AttachLoc ConstraintGenerationError where
  attachLoc loc (SomeConstraintGenerationError _ msg) =
    SomeConstraintGenerationError loc msg

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
-- Errors
----------------------------------------------------------------------------------

data Error where
  ErrConstraintGeneration :: ConstraintGenerationError -> Error
  ErrResolution           :: ResolutionError           -> Error
  ErrConstraintSolver     :: ConstraintSolverError     -> Error
  ErrTypeAutomaton        :: TypeAutomatonError        -> Error
  --
  ParserError           :: Loc -> Text          -> Error
  EvalError             :: Loc -> Text          -> Error
  OtherError            :: Loc -> Text          -> Error
  deriving (Show)

instance HasLoc Error where
  getLoc (ErrConstraintGeneration err) = getLoc err
  getLoc (ErrResolution err) = getLoc err
  getLoc (ErrConstraintSolver err) = getLoc err
  getLoc (ErrTypeAutomaton err) = getLoc err
  --
  getLoc (ParserError loc _) = loc
  getLoc (EvalError loc _) = loc
  getLoc (OtherError loc _) = loc

instance AttachLoc Error where
  attachLoc loc (ErrConstraintGeneration err) = ErrConstraintGeneration (attachLoc loc err)
  attachLoc loc (ErrResolution err) = ErrResolution (attachLoc loc err)
  attachLoc loc (ErrConstraintSolver err) = ErrConstraintSolver (attachLoc loc err)
  attachLoc loc (ErrTypeAutomaton err) = ErrTypeAutomaton (attachLoc loc err)
  --
  attachLoc loc (ParserError _ msg) = ParserError loc msg
  attachLoc loc (EvalError _ txt) = EvalError loc txt
  attachLoc loc (OtherError _ txt) = OtherError loc txt

---------------------------------------------------------------------------------------------
-- Throwing errors in a monadic context
---------------------------------------------------------------------------------------------

throwGenError :: MonadError (NonEmpty Error) m
              => Loc -> [Text] -> m a
throwGenError loc =
  throwError . (NE.:| []) . (ErrConstraintGeneration . SomeConstraintGenerationError loc) . T.unlines

throwEvalError :: MonadError (NonEmpty Error) m
               => Loc -> [Text] -> m a
throwEvalError loc =
  throwError . (NE.:| []) . EvalError loc . T.unlines

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
  throwError . (NE.:| []) . OtherError loc . T.unlines


---------------------------------------------------------------------------------------------
-- Warnings
---------------------------------------------------------------------------------------------

data Warning where
  Warning :: Loc -> Text -> Warning

deriving instance Show Warning

instance HasLoc Warning where
  getLoc (Warning loc _) =
    loc

instance AttachLoc Warning where
  attachLoc loc (Warning _ msg) =
    Warning loc msg