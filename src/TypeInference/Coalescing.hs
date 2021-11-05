module TypeInference.Coalescing where

import Data.Map (Map)

import Syntax.Types
import TypeInference.Constraints

type Bisubstitution = (Map TVar (Typ Pos), Map TVar (Typ Neg))

coalesce :: SolverResult -> Bisubstitution
coalesce = undefined

zonk :: Bisubstitution -> Typ pol -> Typ pol
zonk = undefined