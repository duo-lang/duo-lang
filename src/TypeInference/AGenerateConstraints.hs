module TypeInference.AGenerateConstraints
  ( agenerateConstraints
  , typedATermToType
  ) where

import Syntax.ATerms
import Syntax.Types
import Syntax.Program
import Utils

agenerateConstraints :: ATerm () -> Environment -> Either Error (ATerm SimpleType, ConstraintSet)
agenerateConstraints = undefined

typedATermToType :: Environment -> ATerm SimpleType -> Either Error SimpleType
typedATermToType = undefined

