module Syntax.Types where

import Data.List (nub)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Text (Text)

import Syntax.CommonTerm
    ( XtorName(..),
      NominalStructural(..),
      PrdCnsRep(..),
      PrdCns(..) )
import Syntax.Kinds ( Kind )

------------------------------------------------------------------------------
-- Type Variables and Names
------------------------------------------------------------------------------

-- | Type variables
newtype TVar = MkTVar { tvar_name :: Text } deriving (Eq, Show, Ord)

-- | Name of nominal type
newtype TypeName = MkTypeName { unTypeName :: Text } deriving (Eq, Show, Ord)

------------------------------------------------------------------------------
-- Polarity
------------------------------------------------------------------------------

data Polarity = Pos | Neg deriving (Eq, Ord, Show)

data PolarityRep pol where
  PosRep :: PolarityRep Pos
  NegRep :: PolarityRep Neg
deriving instance Show (PolarityRep pol)
deriving instance Eq (PolarityRep pol)
deriving instance Ord (PolarityRep pol)

flipPol :: Polarity -> Polarity
flipPol Pos = Neg
flipPol Neg = Pos

type family FlipPol (pol :: Polarity) :: Polarity where
  FlipPol Pos = Neg
  FlipPol Neg = Pos

flipPolarityRep :: forall pol. PolarityRep pol -> PolarityRep (FlipPol pol)
flipPolarityRep PosRep = NegRep
flipPolarityRep NegRep = PosRep

polarityRepToPol :: PolarityRep pol -> Polarity
polarityRepToPol PosRep = Pos
polarityRepToPol NegRep = Neg

------------------------------------------------------------------------------
-- Tags
------------------------------------------------------------------------------

data DataCodata = Data | Codata deriving (Eq, Ord, Show)

data DataCodataRep (dc :: DataCodata) where
  DataRep :: DataCodataRep Data
  CodataRep :: DataCodataRep Codata
deriving instance Show (DataCodataRep pol)
deriving instance Eq (DataCodataRep pol)
deriving instance Ord (DataCodataRep pol)

------------------------------------------------------------------------------
-- LinearContexts
------------------------------------------------------------------------------

data PrdCnsType (pol :: Polarity) where
  PrdType :: Typ pol -> PrdCnsType pol
  CnsType :: Typ (FlipPol pol) -> PrdCnsType pol

deriving instance Eq (PrdCnsType Pos)
deriving instance Eq (PrdCnsType Neg)
deriving instance Ord (PrdCnsType Pos)
deriving instance Ord (PrdCnsType Neg)
deriving instance Show (PrdCnsType Pos)
deriving instance Show (PrdCnsType Neg)

type LinearContext pol = [PrdCnsType pol]

------------------------------------------------------------------------------
-- Types
------------------------------------------------------------------------------

data XtorSig (pol :: Polarity) = MkXtorSig
  { sig_name :: XtorName
  , sig_args :: LinearContext pol
  }

deriving instance Eq (XtorSig Pos)
deriving instance Eq (XtorSig Neg)
deriving instance Ord (XtorSig Pos)
deriving instance Ord (XtorSig Neg)
deriving instance Show (XtorSig Pos)
deriving instance Show (XtorSig Neg)

data Typ (pol :: Polarity) where
  TyVar :: PolarityRep pol -> Maybe Kind -> TVar -> Typ pol
  -- | We have to duplicate TyStructData and TyStructCodata here due to restrictions of the deriving mechanism of Haskell.
  -- | Refinement types are represented by the presence of the TypeName parameter
  TyData   :: PolarityRep pol -> Maybe TypeName -> [XtorSig pol]   -> Typ pol
  TyCodata :: PolarityRep pol -> Maybe TypeName -> [XtorSig (FlipPol pol)] -> Typ pol
  TyNominal :: PolarityRep pol -> Maybe Kind -> TypeName -> Typ pol
  -- | PosRep = Union, NegRep = Intersection
  TySet :: PolarityRep pol -> Maybe Kind -> [Typ pol] -> Typ pol
  TyRec :: PolarityRep pol -> TVar -> Typ pol -> Typ pol

deriving instance Eq (Typ Pos)
deriving instance Eq (Typ Neg)
deriving instance Ord (Typ Pos)
deriving instance Ord (Typ Neg)
deriving instance Show (Typ Pos)
deriving instance Show (Typ Neg)

getPolarity :: Typ pol -> PolarityRep pol
getPolarity (TyVar rep _ _)       = rep
getPolarity (TyData rep _ _)      = rep
getPolarity (TyCodata rep _ _)    = rep
getPolarity (TyNominal rep _ _)   = rep
getPolarity (TySet rep _ _)       = rep
getPolarity (TyRec rep _ _)       = rep

-- | Make the XtorName of an XtorSig structural
xtorSigMakeStructural :: XtorSig pol -> XtorSig pol
xtorSigMakeStructural (MkXtorSig (MkXtorName _ s) typArgs) =
  MkXtorSig (MkXtorName Structural s) typArgs

-- | We map producer terms to positive types, and consumer terms to negative types.
type family PrdCnsToPol (pc :: PrdCns) :: Polarity where
  PrdCnsToPol Prd = Pos
  PrdCnsToPol Cns = Neg

prdCnsToPol :: PrdCnsRep pc -> PolarityRep (PrdCnsToPol pc)
prdCnsToPol PrdRep = PosRep
prdCnsToPol CnsRep = NegRep

------------------------------------------------------------------------------
-- Type Schemes
------------------------------------------------------------------------------

data TypeScheme (pol :: Polarity) = TypeScheme
  { ts_vars :: [TVar]
  , ts_monotype :: Typ pol
  }

deriving instance Eq (TypeScheme Pos)
deriving instance Eq (TypeScheme Neg)
deriving instance Ord (TypeScheme Pos)
deriving instance Ord (TypeScheme Neg)

freeTypeVars :: Typ pol -> [TVar]
freeTypeVars = nub . freeTypeVars'
  where
    freeTypeVars' :: Typ pol -> [TVar]
    freeTypeVars' (TyVar _ _ tv) = [tv]
    freeTypeVars' (TySet _ _ ts) = concat $ map freeTypeVars' ts
    freeTypeVars' (TyRec _ v t)  = filter (/= v) (freeTypeVars' t)
    freeTypeVars' (TyNominal _ _ _) = []
    freeTypeVars' (TyData _ _ xtors) = concat (map freeTypeVarsXtorSig  xtors)
    freeTypeVars' (TyCodata _ _ xtors) = concat (map freeTypeVarsXtorSig  xtors)

    freeTypeVarsPC :: PrdCnsType pol -> [TVar]
    freeTypeVarsPC (PrdType ty) = freeTypeVars' ty
    freeTypeVarsPC (CnsType ty) = freeTypeVars' ty

    freeTypeVarsCtxt :: LinearContext pol -> [TVar]
    freeTypeVarsCtxt ctxt = concat (freeTypeVarsPC <$> ctxt)

    freeTypeVarsXtorSig :: XtorSig pol -> [TVar]
    freeTypeVarsXtorSig (MkXtorSig _ ctxt) = freeTypeVarsCtxt ctxt


-- | Generalize over all free type variables of a type.
generalize :: Typ pol -> TypeScheme pol
generalize ty = TypeScheme (freeTypeVars ty) ty

------------------------------------------------------------------------------
-- Substitution
------------------------------------------------------------------------------

-- This is probably not 100% correct w.r.t alpha-renaming. Postponed until we have a better repr. of types.
unfoldRecType :: Typ pol -> Typ pol
unfoldRecType recty@(TyRec PosRep var ty) = substituteType (M.fromList [(var,(recty, error "unfoldRecType"))]) ty
unfoldRecType recty@(TyRec NegRep var ty) = substituteType (M.fromList [(var,(error "unfoldRecType",recty))]) ty
unfoldRecType ty = ty

substituteType :: Map TVar (Typ Pos, Typ Neg) -> Typ pol -> Typ pol
substituteType m var@(TyVar PosRep _ tv) =
  case M.lookup tv m of
    Nothing -> var
    Just (ty,_) -> ty
substituteType m var@(TyVar NegRep _ tv) =
  case M.lookup tv m of
    Nothing -> var
    Just (_,ty) -> ty
-- Other cases
substituteType m (TyData polrep mtn args) = TyData polrep mtn (substituteXtorSig m <$> args)
substituteType m (TyCodata polrep mtn args) = TyCodata polrep mtn (substituteXtorSig m <$> args)
substituteType _ ty@(TyNominal _ _ _) = ty
substituteType m (TySet rep kind args) = TySet rep kind (substituteType m <$> args)
substituteType m (TyRec rep tv arg) = TyRec rep tv (substituteType m arg)

substituteXtorSig :: Map TVar (Typ Pos, Typ Neg) -> XtorSig pol -> XtorSig pol
substituteXtorSig m MkXtorSig { sig_name, sig_args } =  MkXtorSig sig_name (substituteContext m sig_args)

substituteContext :: Map TVar (Typ Pos, Typ Neg) -> LinearContext pol -> LinearContext pol
substituteContext m ctxt = substitutePCType m <$> ctxt

substitutePCType :: Map TVar (Typ Pos, Typ Neg) -> PrdCnsType pol -> PrdCnsType pol
substitutePCType m (PrdType ty)= PrdType $ substituteType m ty
substitutePCType m (CnsType ty)= CnsType $ substituteType m ty



------------------------------------------------------------------------------
-- Data Type declarations
------------------------------------------------------------------------------

data DataDecl = NominalDecl
  { data_name :: TypeName
  , data_polarity :: DataCodata
  , data_kind :: Kind
  , data_xtors :: forall (pol :: Polarity). PolarityRep pol -> [XtorSig pol]
  }
