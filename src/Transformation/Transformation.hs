module Transformation.Transformation where

import Syntax.CST.Kinds
import Syntax.TST.Program qualified as TST
import Data.Set qualified as Set

transformable :: TST.DataDecl -> Bool
transformable decl = Set.size (allTypeVars (TST.data_kind decl)) == 0