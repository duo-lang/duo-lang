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
deriving instance Eq ResolutionError

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
  attachLoc = undefined


----------------------------------------------------------------------------------
-- Errors emitted during the constraint generation phase
----------------------------------------------------------------------------------

data ConstraintGenerationError where
  SomeConstraintGenerationError :: Loc -> Text -> ConstraintGenerationError

deriving instance Show ConstraintGenerationError
deriving instance Eq ConstraintGenerationError

instance HasLoc ConstraintGenerationError where
  getLoc (SomeConstraintGenerationError loc _) =
    loc

instance AttachLoc ConstraintGenerationError where
  attachLoc loc (SomeConstraintGenerationError _ msg) =
    SomeConstraintGenerationError loc msg

----------------------------------------------------------------------------------
-- Errors
----------------------------------------------------------------------------------

data Error where
  ErrConstraintGeneration :: ConstraintGenerationError -> Error
  ErrResolution           :: ResolutionError           -> Error
  --
  ParserError           :: Loc -> Text          -> Error
  EvalError             :: Loc -> Text          -> Error
  SolveConstraintsError :: Loc -> Text          -> Error
  TypeAutomatonError    :: Loc -> Text          -> Error
  OtherError            :: Loc -> Text          -> Error
  NoImplicitArg         :: Loc -> Text          -> Error
  deriving (Show, Eq)

instance HasLoc Error where
  getLoc (ErrConstraintGeneration err) = getLoc err
  getLoc (ErrResolution err) = getLoc err
  --
  getLoc (ParserError loc _) = loc
  getLoc (EvalError loc _) = loc
  getLoc (SolveConstraintsError loc _) = loc
  getLoc (TypeAutomatonError loc _) = loc
  getLoc (OtherError loc _) = loc
  getLoc (NoImplicitArg loc _) = loc

instance AttachLoc Error where
  attachLoc loc (ErrConstraintGeneration err) = ErrConstraintGeneration (attachLoc loc err)
  attachLoc loc (ErrResolution err) = ErrResolution (attachLoc loc err)
  --
  attachLoc loc (ParserError _ msg) = ParserError loc msg
  attachLoc loc (EvalError _ txt) = EvalError loc txt
  attachLoc loc (SolveConstraintsError _ txt) = SolveConstraintsError loc txt
  attachLoc loc (TypeAutomatonError _ txt) = TypeAutomatonError loc txt
  attachLoc loc (OtherError _ txt) = OtherError loc txt
  attachLoc loc (NoImplicitArg _ txt) = NoImplicitArg loc txt




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
  throwError . (NE.:| []) . SolveConstraintsError loc . T.unlines

throwAutomatonError :: MonadError (NonEmpty Error) m
                    => Loc -> [Text] -> m a
throwAutomatonError loc =
  throwError . (NE.:| []) . TypeAutomatonError loc . T.unlines

throwOtherError :: MonadError (NonEmpty Error) m
                => Loc -> [Text] -> m a
throwOtherError loc =
  throwError . (NE.:| []) . OtherError loc . T.unlines


---------------------------------------------------------------------------------------------
-- Warnings
---------------------------------------------------------------------------------------------

data Warning where
  Warning :: Loc -> Text -> Warning
