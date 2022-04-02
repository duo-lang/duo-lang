module Driver.Environment where

import Data.Map (Map)
import Data.Map qualified as M

import Syntax.Common
import Syntax.AST.Terms ( Command, Term )
import Syntax.AST.Types ( DataDecl, TypeScheme )
import Utils ( Loc )

---------------------------------------------------------------------------------
-- Environment
---------------------------------------------------------------------------------

data Environment = MkEnvironment
  { prdEnv :: Map FreeVarName (Term Prd, Loc, TypeScheme Pos)
  , cnsEnv :: Map FreeVarName (Term Cns, Loc, TypeScheme Neg)
  , cmdEnv :: Map FreeVarName (Command, Loc)
  , declEnv :: [(Loc,DataDecl)]
  }

instance Show Environment where
  show _ = "<Environment>"

instance Semigroup Environment where
  (MkEnvironment prdEnv1 cnsEnv1 cmdEnv1 declEnv1) <> (MkEnvironment prdEnv2 cnsEnv2 cmdEnv2 declEnv2) =
    MkEnvironment { prdEnv = M.union prdEnv1 prdEnv2
                  , cnsEnv = M.union cnsEnv1 cnsEnv2
                  , cmdEnv = M.union cmdEnv1 cmdEnv2
                  , declEnv = declEnv1 ++ declEnv2
                  }

instance Monoid Environment where
  mempty = MkEnvironment
    { prdEnv = M.empty
    , cnsEnv = M.empty
    , cmdEnv = M.empty
    , declEnv = []
    }
