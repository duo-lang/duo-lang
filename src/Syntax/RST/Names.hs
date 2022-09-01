module Syntax.RST.Names where

import Loc ( defaultLoc, Loc )
import Syntax.CST.Names qualified as CST

-- | Resolved TypeName
data RnTypeName =
  MkRnTypeName { rnTnLoc :: Loc
                 -- ^ The location of the definition site of the type name
               , rnTnDoc :: Maybe CST.DocComment
                 -- ^ The comment at the definition site
               , rnTnFp :: Maybe FilePath
                 -- ^ The filepath to the definition site
               , rnTnModule :: CST.ModuleName
                 -- ^ The module where the typename was defined
               , rnTnName :: CST.TypeName
                 -- ^ The typename itself
               }
  deriving (Show, Ord, Eq)

peanoNm :: RnTypeName
peanoNm = MkRnTypeName { rnTnLoc    = defaultLoc
                       , rnTnDoc    = Nothing
                       , rnTnFp     = Nothing 
                       , rnTnModule = CST.MkModuleName "Peano"
                       , rnTnName   = CST.MkTypeName "Nat"
                       }