module Syntax.CST.Names where

import Data.Text (Text)

import Loc ( Loc, defaultLoc )

---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

newtype ModuleName = MkModuleName { unModuleName :: Text } deriving (Eq, Ord, Show)

-- | Name of a primitive operation. Starts with a '#' followed by an uppercase letter.
newtype PrimName = MkPrimName { unPrimName :: Text } deriving (Eq, Ord, Show)

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


-- | Name of a constructor/destructor. Starts with an uppercase letter.
newtype XtorName = MkXtorName { unXtorName :: Text } deriving (Eq, Ord, Show)

-- | Name of nominal type or type synonym.
newtype TypeName = MkTypeName { unTypeName :: Text } deriving (Eq, Show, Ord)

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
                       , rnTnModule = MkModuleName "Peano"
                       , rnTnName   = MkTypeName "Nat"
                       }

-- | Name of a free variable. Starts with a lowercase letter.
newtype FreeVarName = MkFreeVarName { unFreeVarName :: Text } deriving (Eq, Ord, Show)

-- | Type variables
newtype UniTVar = MkUniTVar { unUniTVar :: Text } deriving (Eq, Show, Ord)
newtype SkolemTVar = MkSkolemTVar { unSkolemTVar :: Text} deriving (Eq,Show,Ord)
newtype RecTVar = MkRecTVar {unRecTVar :: Text} deriving (Eq, Show, Ord)

skolemToRecRVar :: SkolemTVar -> RecTVar
skolemToRecRVar (MkSkolemTVar n) = MkRecTVar n

-- | Name of a type class. Starts with an uppercase letter.
newtype ClassName = MkClassName { unClassName :: Text } deriving (Eq, Show, Ord)

-- | Name of a type class method. Starts with an uppercase letter.
newtype MethodName = MkMethodName { unMethodName :: Text } deriving (Eq, Show, Ord)

---------------------------------------------------------------------------------
-- Doc comments
---------------------------------------------------------------------------------

newtype DocComment = MkDocComment { unDocComment :: Text } deriving (Eq, Show, Ord)

---------------------------------------------------------------------------------
-- Type operators
---------------------------------------------------------------------------------

-- | Name of type operators
newtype TyOpName  = MkTyOpName { unTyOpName :: Text } deriving (Eq, Show, Ord)

-- | Binary type operators
data BinOp where
  CustomOp :: TyOpName -> BinOp
  UnionOp  :: BinOp
  InterOp  :: BinOp
  deriving (Show, Eq, Ord)

data Associativity where
  LeftAssoc :: Associativity
  RightAssoc :: Associativity
  deriving (Eq, Show, Ord)

newtype Precedence = MkPrecedence Int
  deriving (Eq, Show, Ord)

---------------------------------------------------------------------------------
-- de Bruijn indices
---------------------------------------------------------------------------------

-- | Two-level de Bruijn indices.
type Index = (Int, Int)
