module Xfunc.Xfunc where

import Syntax.RST.Kinds
import Syntax.TST.Program qualified as TST
import Data.Set qualified as Set

transformable :: TST.DataDecl -> Bool
transformable decl = Set.size (allTypeVars (decl.data_kind)) == 0


-- xfunc a (co)datatype in a module
xfunc :: TST.Module -> TST.DataDecl -> TST.Module
xfunc = undefined