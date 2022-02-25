module Errors where

import Control.Monad.Except
import Data.Text (Text)
import Data.Text qualified as T

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
  deriving (Show, Eq)

data Error where
  ParseError            :: Maybe Loc -> Text -> Error
  GenConstraintsError   :: Maybe Loc -> Text -> Error
  EvalError             :: Maybe Loc -> Text -> Error
  SolveConstraintsError :: Maybe Loc -> Text -> Error
  TypeAutomatonError    :: Maybe Loc -> Text -> Error
  LowerError            :: Maybe Loc -> LoweringError -> Error
  OtherError            :: Maybe Loc -> Text -> Error
  deriving (Show, Eq)

attachLoc :: Loc -> Error -> Error
attachLoc loc (ParseError _ txt) = ParseError (Just loc) txt
attachLoc loc (GenConstraintsError _ txt) = GenConstraintsError (Just loc) txt
attachLoc loc (EvalError _ txt) = EvalError (Just loc) txt
attachLoc loc (SolveConstraintsError _ txt) = SolveConstraintsError (Just loc) txt
attachLoc loc (TypeAutomatonError _ txt) = TypeAutomatonError (Just loc) txt
attachLoc loc (LowerError _ err) = LowerError (Just loc) err
attachLoc loc (OtherError _ txt) = OtherError (Just loc) txt

getLoc :: Error -> Maybe Loc
getLoc (ParseError loc _)  = loc
getLoc (GenConstraintsError loc _) = loc
getLoc (EvalError loc _) = loc
getLoc (SolveConstraintsError loc _) = loc
getLoc (TypeAutomatonError loc _) = loc
getLoc (LowerError loc _) = loc
getLoc (OtherError loc _) = loc

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
