module TypeInference.AGenerateConstraints
  ( agenerateConstraints
  , typedATermToType
  ) where

import Control.Monad.State
import Control.Monad.Except

import Syntax.ATerms
import Syntax.Types
import Syntax.Program
import Utils

data GenerateState = GenerateState { varCount :: Int }

initialState :: GenerateState
initialState = GenerateState 0

type GenM a = StateT GenerateState (Except Error) a

runGenM :: GenerateState -> GenM a -> Either Error a
runGenM initState m = runExcept (evalStateT m initState)

freshTVar :: GenM SimpleType
freshTVar = do
  var <- gets varCount
  modify (\gs@GenerateState{ varCount } -> gs { varCount = var + 1 })
  return (TyVar Normal (MkTVar (show var)))

genConstraints :: ATerm () -> GenM (ATerm SimpleType)
genConstraints (BVar idx) = undefined
genConstraints (FVar fv) = undefined
genConstraints (Ctor xt args) = undefined
genConstraints (Dtor xt t args) = undefined
genConstraints (Match t cases) = undefined
genConstraints (Comatch cocases) = undefined

agenerateConstraints :: ATerm () -> Environment -> Either Error (ATerm SimpleType, ConstraintSet)
agenerateConstraints = undefined

typedATermToType :: Environment -> ATerm SimpleType -> Either Error SimpleType
typedATermToType = undefined

