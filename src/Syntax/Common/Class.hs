module Syntax.Common.Class where

import Syntax.Common
import Syntax.Common.TypesUnpol (Typ)
import Syntax.CST.Terms (TermCase)

------------------------------------------------------------------------------
-- Instance definition
------------------------------------------------------------------------------

data InstanceDecl = InstanceDecl
  { instance_name :: ClassName
  , instance_typ :: Typ
  , instance_cases :: [TermCase]
  }

deriving instance (Show InstanceDecl)

------------------------------------------------------------------------------
-- Class declarations
------------------------------------------------------------------------------

data ClassDecl = ClassDecl
  { class_name :: ClassName
  , class_kinds :: [(Variance, TVar, MonoKind)]
  , class_xtors :: [(XtorName, [(PrdCns, Typ)])]
  }

deriving instance (Show ClassDecl)