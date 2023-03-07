module Syntax.CST.Names where

import Data.Text (Text)

import Data.Aeson (ToJSON, FromJSON)
import GHC.Generics (Generic)

---------------------------------------------------------------------------------
-- Names
---------------------------------------------------------------------------------

data ModuleName = MkModuleName { mn_path :: [Text], mn_base :: Text } deriving (Eq, Ord, Show)

-- | Name of a primitive operation. Starts with a '#' followed by an uppercase letter.
newtype PrimName = MkPrimName { unPrimName :: Text } deriving (Eq, Ord, Show)

-- | Name of a constructor/destructor. Starts with an uppercase letter.
newtype XtorName = MkXtorName { unXtorName :: Text } deriving (Eq, Ord, Show)

-- | Name of nominal type or type synonym.
newtype TypeName = MkTypeName { unTypeName :: Text } deriving (Eq, Show, Ord)

-- | Name of a free variable. Starts with a lowercase letter.
newtype FreeVarName = MkFreeVarName { unFreeVarName :: Text }
  deriving stock (Eq, Ord, Show, Generic)
  deriving newtype (FromJSON, ToJSON)

-- | Type variables

newtype SkolemTVar = MkSkolemTVar { unSkolemTVar :: Text} deriving (Eq,Show,Ord)

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
