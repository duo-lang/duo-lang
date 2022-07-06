module Errors where

import Control.Monad.Except
import Data.Text (Text)
import Data.Text qualified as T
import Data.List.NonEmpty (NonEmpty)

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

data ParserError = MkParserError Loc Text
  deriving (Show, Eq)

data Error where
  ParserErrorBundle     :: NonEmpty ParserError       -> Error
  GenConstraintsError   :: Maybe Loc -> Text          -> Error
  EvalError             :: Maybe Loc -> Text          -> Error
  SolveConstraintsError :: Maybe Loc -> Text          -> Error
  TypeAutomatonError    :: Maybe Loc -> Text          -> Error
  LowerError            :: Maybe Loc -> LoweringError -> Error
  OtherError            :: Maybe Loc -> Text          -> Error
  NoImplicitArg         :: Maybe Loc -> Text          -> Error
  deriving (Show, Eq)

attachLoc :: Loc -> Error -> Error
attachLoc _   err@(ParserErrorBundle _) = err
attachLoc loc (GenConstraintsError _ txt) = GenConstraintsError (Just loc) txt
attachLoc loc (EvalError _ txt) = EvalError (Just loc) txt
attachLoc loc (SolveConstraintsError _ txt) = SolveConstraintsError (Just loc) txt
attachLoc loc (TypeAutomatonError _ txt) = TypeAutomatonError (Just loc) txt
attachLoc loc (LowerError _ err) = LowerError (Just loc) err
attachLoc loc (OtherError _ txt) = OtherError (Just loc) txt
attachLoc loc (NoImplicitArg _ txt) = NoImplicitArg (Just loc) txt

getLoc :: Error -> Maybe Loc
getLoc (ParserErrorBundle _)  = Nothing
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

throwGenError :: MonadError Error m
              => [Text] -> m a
throwGenError = throwError . GenConstraintsError Nothing . T.unlines

throwEvalError :: MonadError Error m
               => [Text] -> m a
throwEvalError = throwError . EvalError Nothing . T.unlines

throwSolverError :: MonadError Error m
                 => [Text] -> m a
throwSolverError = throwError . SolveConstraintsError Nothing . T.unlines

throwAutomatonError :: MonadError Error m
                    => [Text] -> m a
throwAutomatonError = throwError . TypeAutomatonError Nothing . T.unlines

throwOtherError :: MonadError Error m
                => [Text] -> m a
throwOtherError = throwError . OtherError Nothing . T.unlines


---------------------------------------------------------------------------------------------
-- Warnings
---------------------------------------------------------------------------------------------

data Warning where
  Warning :: Loc -> Text -> Warning
