{-# LANGUAGE MultiParamTypeClasses #-}

module TypeInference.Derive
    ( Derivable(..)
    ) where

import Syntax.Common.TypesPol
import Syntax.Common (Polarity)

-- | Defines the relationship between types for which we can derive an instance
-- based on a given defind instance similar but not as strict as Eq.
class Derivable a b where
    -- | Check whether an instance for a can be derived from an instance of b.
    derivable :: a -> b -> Bool
    -- | Check whether instance is derivable from one in a list of instances.
    occursIn :: a -> [b] -> Bool
    occursIn x ys = any (derivable x) ys
    {-# MINIMAL derivable #-}

instance Derivable (Typ (pol :: Polarity)) (Typ (pol :: Polarity)) where
    derivable TyData{}                TyData{}                = False
    derivable TyCodata{}              TyCodata{}              = False
    derivable TyDataRefined{}         TyDataRefined{}         = False
    derivable TyCodataRefined{}       TyCodataRefined{}       = False
    derivable (TyNominal _ _ _ rn1 _) (TyNominal _ _ _ rn2 _) = rn1 == rn2
    derivable TyBot{}                 _                       = True
    derivable _                       TyTop{}                 = True
    derivable TyUnion{}               TyUnion{}               = False
    derivable TyInter{}               TyInter{}               = False
    derivable TyRec{}                 TyRec{}                 = False
    derivable (TyPrim _ _ t1)         (TyPrim _ _ t2)         = t1 == t2
    derivable TyFlipPol{}             TyFlipPol{}             = False
    derivable TySkolemVar{}           _                       = True
    derivable TyUniVar{}              _                       = True
    derivable _                       _                       = False
