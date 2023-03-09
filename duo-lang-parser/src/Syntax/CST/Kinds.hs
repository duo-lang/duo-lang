 module Syntax.CST.Kinds where


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



------------------------------------------------------------------------------
-- Kinds
------------------------------------------------------------------------------

data PolyKind =
  MkPolyKind { kindArgs :: [(Variance, SkolemTVar, MonoKind)]
             , returnKind :: EvaluationOrder
             }
  | KindVar KVar 

deriving instance (Show PolyKind)
deriving instance (Eq PolyKind)
deriving instance (Ord PolyKind)
