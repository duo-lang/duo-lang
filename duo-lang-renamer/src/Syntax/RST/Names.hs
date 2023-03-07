module Syntax.RST.Names where

import Data.Text
import Loc
import Syntax.CST.Names

newtype RecTVar = MkRecTVar {unRecTVar :: Text} deriving (Eq, Show, Ord)
newtype UniTVar = MkUniTVar { unUniTVar :: Text } deriving (Eq, Show, Ord)

skolemToRecRVar :: SkolemTVar -> RecTVar
skolemToRecRVar (MkSkolemTVar n) = MkRecTVar n

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

printName :: PrimName
printName = MkPrimName "Print"

readName :: PrimName
readName = MkPrimName "Read"

exitSuccessName :: PrimName
exitSuccessName = MkPrimName "ExitSuccess"

exitFailureName :: PrimName
exitFailureName = MkPrimName "ExitFailure"

i64AddName :: PrimName
i64AddName = MkPrimName "I64Add"

i64SubName :: PrimName
i64SubName = MkPrimName "I64Sub"

i64MulName :: PrimName
i64MulName = MkPrimName "I64Mul"

i64DivName :: PrimName
i64DivName = MkPrimName "I64Div"

i64ModName :: PrimName
i64ModName = MkPrimName "I64Mod"

f64AddName :: PrimName
f64AddName = MkPrimName "F64Add"

f64SubName :: PrimName
f64SubName = MkPrimName "F64Sub"

f64MulName :: PrimName
f64MulName = MkPrimName "F64Mul"

f64DivName :: PrimName
f64DivName = MkPrimName "F64Div"

charPrependName :: PrimName
charPrependName = MkPrimName "CharPrepend"

stringAppendName :: PrimName
stringAppendName = MkPrimName "StringAppend"