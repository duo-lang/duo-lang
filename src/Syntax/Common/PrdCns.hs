module Syntax.Common.PrdCns where

import Syntax.Common.Polarity

data PrdCns
  = Prd
  | Cns
  deriving (Eq, Show, Ord)

-- | Singleton Type for PrdCns
data PrdCnsRep pc where
  PrdRep :: PrdCnsRep Prd
  CnsRep :: PrdCnsRep Cns
deriving instance Show (PrdCnsRep pc)
deriving instance Eq (PrdCnsRep pc)

type family FlipPrdCns (pc :: PrdCns) :: PrdCns where
  FlipPrdCns Prd = Cns
  FlipPrdCns Cns = Prd

flipPrdCns :: PrdCnsRep pc -> PrdCnsRep (FlipPrdCns pc)
flipPrdCns PrdRep = CnsRep
flipPrdCns CnsRep = PrdRep

type family PrdCnsFlip (pc :: PrdCns) (pol :: Polarity) :: Polarity where
  PrdCnsFlip Prd pol = pol
  PrdCnsFlip Cns pol = FlipPol pol

-- | We map producer terms to positive types, and consumer terms to negative types.
type family PrdCnsToPol (pc :: PrdCns) :: Polarity where
  PrdCnsToPol Prd = Pos
  PrdCnsToPol Cns = Neg

prdCnsToPol :: PrdCnsRep pc -> PolarityRep (PrdCnsToPol pc)
prdCnsToPol PrdRep = PosRep
prdCnsToPol CnsRep = NegRep

type Arity = [PrdCns]
