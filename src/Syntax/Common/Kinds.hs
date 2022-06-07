module Syntax.Common.Kinds where

import Data.Set (Set)
import Data.Set qualified as S

import Syntax.Common.Names
import Syntax.Common.Primitives

---------------------------------------------------------------------------------
-- Variance
---------------------------------------------------------------------------------

data Variance = Covariant | Contravariant
  deriving (Eq, Show, Ord)

instance Semigroup Variance where
  Covariant <> v         = v
  v         <> Covariant = v
  _         <> _         = Covariant

---------------------------------------------------------------------------------
-- Evaluation Order
---------------------------------------------------------------------------------

-- | An evaluation order is either call-by-value or call-by-name.
data EvaluationOrder = CBV | CBN
  deriving (Show, Eq, Ord)

---------------------------------------------------------------------------------
-- MonoKind
---------------------------------------------------------------------------------

-- | A MonoKind is a kind which classifies inhabitated types.
data MonoKind
  = CBox EvaluationOrder  -- ^ Boxed CBV/CBN
  | CRep PrimitiveType    -- ^ Primitive type representation
  deriving (Show, Eq, Ord)

------------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------------

data PolyKind =
  MkPolyKind { kindArgs :: [(Variance, TVar, MonoKind)]
             , returnKind :: EvaluationOrder
             }

deriving instance (Show PolyKind)
deriving instance (Eq PolyKind)

allTypeVars :: PolyKind -> Set TVar
allTypeVars MkPolyKind{ kindArgs } =
  S.fromList ((\(_,var,_) -> var) <$> kindArgs)

lookupPolyKind :: TVar -> PolyKind -> Maybe (Variance, TVar, MonoKind)
lookupPolyKind tv MkPolyKind{ kindArgs } = go kindArgs
  where
    go :: [(Variance, TVar, MonoKind)] -> Maybe (Variance, TVar, MonoKind)
    go [] = Nothing
    go (k@(_,tv',_) : ks) = if tv == tv'
                           then Just k
                           else go ks
lookupPolyKindVariance :: TVar -> PolyKind -> Maybe Variance
lookupPolyKindVariance tv pk = (\(v,_,_) -> v) <$> lookupPolyKind tv pk
