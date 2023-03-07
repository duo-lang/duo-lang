module Syntax.RST.Names where

import Loc
import Syntax.CST.Names

-- | Resolved TypeName
data RnTypeName =
  MkRnTypeName { rnTnLoc :: Loc
                 -- ^ The location of the definition site of the type name
               , rnTnDoc :: Maybe DocComment
                 -- ^ The comment at the definition site
               , rnTnFp :: Maybe FilePath
                 -- ^ The filepath to the definition site
               , rnTnModule :: ModuleName
                 -- ^ The module where the typename was defined
               , rnTnName :: TypeName
                 -- ^ The typename itself
               }
  deriving (Show, Ord, Eq)

peanoNm :: RnTypeName
peanoNm = MkRnTypeName { rnTnLoc    = defaultLoc
                       , rnTnDoc    = Nothing
                       , rnTnFp     = Nothing 
                       , rnTnModule = MkModuleName ["Data"] "Peano" 
                       , rnTnName   = MkTypeName "Nat"
                       }