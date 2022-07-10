module Errors where

import Control.Monad.Except
import Data.List.NonEmpty ( NonEmpty )
import Data.List.NonEmpty qualified as NE
import Data.Text (Text)
import Data.Text qualified as T

import Syntax.Common
import Utils

----------------------------------------------------------------------------------
-- Errors
----------------------------------------------------------------------------------

data LoweringError where
  -- Type scheme violations
  MissingVarsInTypeScheme :: LoweringError
  -- Polarity violations
  TopInPosPolarity :: LoweringError
  BotInNegPolarity :: LoweringError
  IntersectionInPosPolarity :: LoweringError
  UnionInNegPolarity :: LoweringError
  -- Operator errors
  UnknownOperator :: Text -> LoweringError
  XtorArityMismatch :: XtorName
                -> Int
                -> Int
                -> LoweringError
  UndefinedPrimOp :: (PrimitiveType, PrimitiveOp) -> LoweringError
  PrimOpArityMismatch :: (PrimitiveType, PrimitiveOp)
                -> Int
                -> Int
                -> LoweringError
  CmdExpected :: Text -> LoweringError                
  InvalidStar  :: Text
                -> LoweringError
  deriving (Show, Eq)

data Error where
  ParserError           :: Loc -> Text          -> Error
  GenConstraintsError   :: Loc -> Text          -> Error
  EvalError             :: Loc -> Text          -> Error
  SolveConstraintsError :: Loc -> Text          -> Error
  TypeAutomatonError    :: Loc -> Text          -> Error
  LowerError            :: Loc -> LoweringError -> Error
  OtherError            :: Loc -> Text          -> Error
  NoImplicitArg         :: Loc -> Text          -> Error
  deriving (Show, Eq)

attachLoc :: Loc -> Error -> Error
attachLoc loc (ParserError _ msg) = ParserError loc msg
attachLoc loc (GenConstraintsError _ txt) = GenConstraintsError loc txt
attachLoc loc (EvalError _ txt) = EvalError loc txt
attachLoc loc (SolveConstraintsError _ txt) = SolveConstraintsError loc txt
attachLoc loc (TypeAutomatonError _ txt) = TypeAutomatonError loc txt
attachLoc loc (LowerError _ err) = LowerError loc err
attachLoc loc (OtherError _ txt) = OtherError loc txt
attachLoc loc (NoImplicitArg _ txt) = NoImplicitArg loc txt

getLoc :: Error -> Loc
getLoc (ParserError loc _) = loc
getLoc (GenConstraintsError loc _) = loc
getLoc (EvalError loc _) = loc
getLoc (SolveConstraintsError loc _) = loc
getLoc (TypeAutomatonError loc _) = loc
getLoc (LowerError loc _) = loc
getLoc (OtherError loc _) = loc
getLoc (NoImplicitArg loc _) = loc

---------------------------------------------------------------------------------------------
-- Throwing errors in a monadic context
---------------------------------------------------------------------------------------------

throwGenError :: MonadError (NonEmpty Error) m
              => Loc -> [Text] -> m a
throwGenError loc =
  throwError . (NE.:| []) . GenConstraintsError loc . T.unlines

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
