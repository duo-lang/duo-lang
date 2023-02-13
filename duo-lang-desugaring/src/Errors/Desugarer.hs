module Errors.Desugarer where

import Data.Text (Text)
import Loc

data DesugaringError where
    UnknownDesugaringError :: Loc -> Text -> DesugaringError

deriving instance Show DesugaringError

instance HasLoc DesugaringError where
  getLoc :: DesugaringError -> Loc
  getLoc (UnknownDesugaringError loc _) = loc

instance AttachLoc DesugaringError where 
  attachLoc :: Loc -> DesugaringError -> DesugaringError
  attachLoc loc (UnknownDesugaringError _ msg) = UnknownDesugaringError loc msg
