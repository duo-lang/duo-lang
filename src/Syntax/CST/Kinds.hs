module Syntax.CST.Kinds where

import Data.Set (Set)
import Data.Set qualified as S

import Syntax.Common.Names
import Syntax.Common.Primitives
import Data.Text

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
-- Kind Variables
---------------------------------------------------------------------------------

-- | A Kind Variable that is used for inferred kinds
newtype KVar = MkKVar { unKVar :: Text }
  deriving (Show, Eq, Ord)

---------------------------------------------------------------------------------
-- MonoKind
---------------------------------------------------------------------------------

-- | A MonoKind is a kind which classifies inhabitated types.
data MonoKind
  = CBox EvaluationOrder  -- ^ Boxed CBV/CBN
  | CRep PrimitiveType    -- ^ Primitive type representation
  | KindVar KVar 
  deriving (Show, Eq, Ord)

-- | A kind Variable used for top and bottom kinds, as they can have any kind
anyKind::MonoKind
anyKind = KindVar (MkKVar (Data.Text.pack "TopBotKind"))

------------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------------

data PolyKind =
  MkPolyKind { kindArgs :: [(Variance, SkolemTVar, MonoKind)]
             , returnKind :: EvaluationOrder
             }

deriving instance (Show PolyKind)
deriving instance (Eq PolyKind)
deriving instance (Ord PolyKind)

freeKindVars :: MonoKind -> Maybe KVar
freeKindVars (CBox _) = Nothing
freeKindVars (CRep _) = Nothing
freeKindVars (KindVar v) = Just v

allTypeVars :: PolyKind -> Set SkolemTVar
allTypeVars MkPolyKind{ kindArgs } =
  S.fromList ((\(_,var,_) -> var) <$> kindArgs)

lookupPolyKind :: SkolemTVar -> PolyKind -> Maybe (Variance, SkolemTVar, MonoKind)
lookupPolyKind tv MkPolyKind{ kindArgs } = go kindArgs
  where
    go :: [(Variance, SkolemTVar, MonoKind)] -> Maybe (Variance, SkolemTVar, MonoKind)
    go [] = Nothing
    go (k@(_,tv',_) : ks) = if tv == tv'
                           then Just k
                           else go ks

lookupPolyKindVariance :: SkolemTVar -> PolyKind -> Maybe Variance
lookupPolyKindVariance tv pk = (\(v,_,_) -> v) <$> lookupPolyKind tv pk
