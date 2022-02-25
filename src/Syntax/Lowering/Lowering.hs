module Syntax.Lowering.Lowering
  ( LoweringError(..)
  , LowerM
  , runLowerM
  ) where

import Control.Monad.Except
import Data.Text (Text)
import Data.Text qualified as T

import Syntax.CST.Types (BinOp)

data LoweringError where
    -- Type scheme violations
    MissingVarsInTypeScheme :: LoweringError
    -- Polarity violations
    TopInPosPolarity :: LoweringError
    BotInNegPolarity :: LoweringError
    IntersectionInPosPolarity :: LoweringError
    UnionInNegPolarity :: LoweringError
    -- Operator errors
    UnknownOperator :: BinOp -> LoweringError
    OtherError :: Text -> LoweringError

instance Show LoweringError where
    show MissingVarsInTypeScheme = "Missing declaration of type variable"
    show TopInPosPolarity = "Cannot use `Top` in positive polarity"
    show BotInNegPolarity = "Cannot use `Bot` in negative polarity"
    show IntersectionInPosPolarity = "Cannot use `/\\` in positive polarity"
    show UnionInNegPolarity = "Cannot use `\\/` in negative polarity"
    show (UnknownOperator op) = "Undefined type operator `" ++ show op ++ "`"
    show (OtherError txt) = T.unpack txt

newtype LowerM a = MkLowerM { unLowerM :: Except LoweringError a }
  deriving (Functor, Applicative, Monad, MonadError LoweringError)

runLowerM :: LowerM a -> Either LoweringError a
runLowerM m = runExcept (unLowerM m)