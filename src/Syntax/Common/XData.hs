module Syntax.Common.XData where

data DataCodata = Data | Codata deriving (Eq, Ord, Show)

data DataCodataRep (dc :: DataCodata) where
  DataRep :: DataCodataRep Data
  CodataRep :: DataCodataRep Codata

deriving instance Show (DataCodataRep pol)
deriving instance Eq (DataCodataRep pol)
deriving instance Ord (DataCodataRep pol)
