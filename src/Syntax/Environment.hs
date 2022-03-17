module Syntax.Environment where

import Data.Map (Map)
import Data.Map qualified as M

import Syntax.Common
import Syntax.AST.Terms
import Syntax.AST.Types
import Syntax.Kinds
import Utils

---------------------------------------------------------------------------------
-- SymbolTable
---------------------------------------------------------------------------------

data SymbolTable = MkSymbolTable {
     xtorMap :: Map (XtorName,DataCodata) (NominalStructural, Arity),
     tyConMap :: Map TypeName (IsRefined, DataCodata, TParams, Kind)
}

instance Semigroup SymbolTable where
  (MkSymbolTable m1 m2) <> (MkSymbolTable m1' m2') =
    MkSymbolTable (M.union m1 m1') (M.union m2 m2')

instance Monoid SymbolTable where
  mempty = MkSymbolTable M.empty M.empty

---------------------------------------------------------------------------------
-- Environment
---------------------------------------------------------------------------------

data Environment (ph :: Phase) = MkEnvironment
  { prdEnv :: Map FreeVarName (Term Prd ph, Loc, TypeScheme Pos)
  , cnsEnv :: Map FreeVarName (Term Cns ph, Loc, TypeScheme Neg)
  , cmdEnv :: Map FreeVarName (Command ph, Loc)
  , declEnv :: [(Loc,DataDecl)]
  , symTable :: SymbolTable
  }

instance Show (Environment ph) where
  show _ = "<Environment>"

instance Semigroup (Environment ph) where
  (MkEnvironment prdEnv1 cnsEnv1 cmdEnv1 declEnv1 symTable1) <> (MkEnvironment prdEnv2 cnsEnv2 cmdEnv2 declEnv2 symTable2) =
    MkEnvironment { prdEnv = M.union prdEnv1 prdEnv2
                  , cnsEnv = M.union cnsEnv1 cnsEnv2
                  , cmdEnv = M.union cmdEnv1 cmdEnv2
                  , declEnv = declEnv1 ++ declEnv2
                  , symTable = symTable1 <> symTable2
                  }

instance Monoid (Environment ph) where
  mempty = MkEnvironment
    { prdEnv = M.empty
    , cnsEnv = M.empty
    , cmdEnv = M.empty
    , declEnv = []
    , symTable = mempty
    }
