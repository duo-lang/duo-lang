module Xfunc.Xfunc where

import Syntax.CST.Kinds
import Syntax.TST.Program qualified as TST
import Data.Set qualified as Set

transformable :: TST.DataDecl -> Bool
transformable decl = Set.size (allTypeVars (decl.data_kind)) == 0