module Syntax.Common.Names where

import Data.Text (Text)

newtype ModuleName = MkModuleName { unModuleName :: Text } deriving (Eq, Ord, Show)

-- | Name of a constructor/destructor. Starts with an uppercase letter.
newtype XtorName = MkXtorName { unXtorName :: Text } deriving (Eq, Ord, Show)

-- | Name of nominal type
newtype TypeName = MkTypeName { unTypeName :: Text } deriving (Eq, Show, Ord)

-- | Name of a free variable. Starts with a lowercase letter.
newtype FreeVarName = MkFreeVarName { unFreeVarName :: Text } deriving (Eq, Ord, Show)

-- | Type variables
newtype TVar = MkTVar { unTVar :: Text } deriving (Eq, Show, Ord)

-- | Name of type operators
newtype TyOpName  = MkTyOpName { unTyOpName :: Text } deriving (Eq, Show, Ord)

-- | Binary type operators
data BinOp where
  CustomOp :: TyOpName -> BinOp
  UnionOp  :: BinOp
  InterOp  :: BinOp
  deriving (Show, Eq)

-- | Two-level de Bruijn indices.
type Index = (Int, Int)
