 module Syntax.CST.Kinds where

import Data.Set (Set)
import Data.Set qualified as S


import Data.Text
import Syntax.CST.Names

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
  | I64Rep
  | F64Rep
  | CharRep
  | StringRep
  deriving (Show, Eq, Ord)

type MaybeKindedSkolem = (SkolemTVar, Maybe PolyKind)
type KindedSkolem = (SkolemTVar,PolyKind)


------------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------------

data PolyKind =
  MkPolyKind { kindArgs :: [(Variance, SkolemTVar, MonoKind)]
             , returnKind :: EvaluationOrder
             }
  | KindVar KVar 

deriving instance (Show PolyKind)
deriving instance (Ord PolyKind)
instance Eq PolyKind where 
  KindVar kv1 == KindVar kv2 = kv1 == kv2
  MkPolyKind args1 eo1 == MkPolyKind args2 eo2 = 
    let getVariances = Prelude.map (\(x,_,_) -> x)
        getMks = Prelude.map (\(_,_,z) -> z)
    in 
    eo1 == eo2 && getVariances args1 == getVariances args2 && getMks args1 == getMks args2
  _ == _ = False 


--either polykind or primitive kind
data AnyKind = MkPknd PolyKind | MkI64 | MkF64 | MkChar | MkString 
deriving instance (Show AnyKind)
deriving instance (Ord AnyKind)
deriving instance (Eq AnyKind)

monoToAnyKind :: MonoKind -> AnyKind
monoToAnyKind (CBox eo) = MkPknd (MkPolyKind [] eo)
monoToAnyKind I64Rep = MkI64
monoToAnyKind F64Rep = MkF64
monoToAnyKind CharRep = MkChar
monoToAnyKind StringRep = MkString

allTypeVars :: PolyKind -> Set SkolemTVar
allTypeVars pk@MkPolyKind{} = S.fromList ((\(_,var,_) -> var) <$> pk.kindArgs)
allTypeVars (KindVar _) = S.empty

lookupPolyKind :: SkolemTVar -> PolyKind -> Maybe (Variance, SkolemTVar, MonoKind)
lookupPolyKind tv pk@MkPolyKind{} = go pk.kindArgs
  where
    go :: [(Variance, SkolemTVar, MonoKind)] -> Maybe (Variance, SkolemTVar, MonoKind)
    go [] = Nothing
    go (k@(_,tv',_) : ks) = if tv == tv'
                           then Just k
                           else go ks
lookupPolyKind _ (KindVar _) = Nothing

lookupPolyKindVariance :: SkolemTVar -> PolyKind -> Maybe Variance
lookupPolyKindVariance tv pk = (\(v,_,_) -> v) <$> lookupPolyKind tv pk
