module Syntax.RST.Kinds where

import Data.Set (Set)
import Data.Set qualified as S

import Syntax.CST.Types
import Syntax.CST.Names

--either polykind or primitive kind
data AnyKind = MkPknd PolyKind | MkI64 | MkF64 | MkChar | MkString 
deriving instance (Show AnyKind)
deriving instance (Eq AnyKind)
deriving instance (Ord AnyKind)

type KindedSkolem = (SkolemTVar,PolyKind)

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
