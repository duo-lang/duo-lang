module Driver.Environment where

import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)

import Syntax.Common
import Syntax.TST.Terms ( Command, Term )
import Syntax.RST.Program ( ClassDeclaration )
import Syntax.Common.TypesPol ( DataDecl, TypeScheme, Typ )
import Utils ( Loc )

---------------------------------------------------------------------------------
-- Environment
---------------------------------------------------------------------------------

data Environment = MkEnvironment
  { prdEnv :: Map FreeVarName (Term Prd, Loc, TypeScheme Pos)
  , cnsEnv :: Map FreeVarName (Term Cns, Loc, TypeScheme Neg)
  , cmdEnv :: Map FreeVarName (Command, Loc)
  , classEnv :: Map ClassName ClassDeclaration
  , instanceEnv :: Map ClassName (Set (Typ Pos, Typ Neg))
  , declEnv :: [(Loc,DataDecl)]
  }

emptyEnvironment :: Environment
emptyEnvironment = MkEnvironment M.empty M.empty M.empty M.empty M.empty []
instance Show Environment where
  show _ = "<Environment>"
