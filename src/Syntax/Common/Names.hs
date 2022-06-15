module Syntax.Common.Names where

import Data.Text (Text)

import Utils

---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

newtype ModuleName = MkModuleName { unModuleName :: Text } deriving (Eq, Ord, Show)

-- | Name of a constructor/destructor. Starts with an uppercase letter.
newtype XtorName = MkXtorName { unXtorName :: Text } deriving (Eq, Ord, Show)

-- | Name of nominal type or type synonym.
newtype TypeName = MkTypeName { unTypeName :: Text } deriving (Eq, Show, Ord)

-- | Resolved TypeName
-- rnTnLoc contains location of definition site.
data RnTypeName = MkRnTypeName { rnTnLoc :: Loc, rnTnDoc :: Maybe DocComment, rnTnModule :: ModuleName, rnTnName :: TypeName }
  deriving (Show, Ord, Eq)

peanoNm :: RnTypeName
peanoNm = MkRnTypeName defaultLoc Nothing (MkModuleName "Peano")(MkTypeName "Nat")

-- | Name of a free variable. Starts with a lowercase letter.
newtype FreeVarName = MkFreeVarName { unFreeVarName :: Text } deriving (Eq, Ord, Show)

-- | Type variables
newtype TVar = MkTVar { unTVar :: Text } deriving (Eq, Show, Ord)

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
  deriving (Show, Eq)

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
