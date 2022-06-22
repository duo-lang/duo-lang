module Syntax.Common.Pattern where
import Utils (Loc)
import Syntax.Common.Names
import Syntax.Common.PrdCns
---------------------------------------------------------------------------------
-- Pattern/copattern match cases
---------------------------------------------------------------------------------

data Pattern where
  XtorPat :: Loc -> XtorName -> [(PrdCns, Maybe FreeSkolemVarName)] -> Pattern

deriving instance Eq Pattern
deriving instance Show Pattern

data PatternI where
  XtorPatI :: Loc -> XtorName -> ([(PrdCns, Maybe FreeSkolemVarName)], (), [(PrdCns, Maybe FreeSkolemVarName)]) -> PatternI
deriving instance Eq PatternI
deriving instance Show PatternI
