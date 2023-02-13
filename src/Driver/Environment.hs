module Driver.Environment where

import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)

import Syntax.CST.Names
import Syntax.TST.Terms ( Command, Term )
import Syntax.RST.Program ( ClassDeclaration, StructuralXtorDeclaration)
import Syntax.TST.Types ( TypeScheme, Typ )
import Syntax.TST.Program ( DataDecl, InstanceDeclaration )
import Syntax.RST.Types (Polarity(..))
import Syntax.CST.Types( PrdCns(..) )
import Syntax.CST.Kinds (EvaluationOrder)
import Loc ( Loc )

---------------------------------------------------------------------------------
-- Environment
---------------------------------------------------------------------------------

data Environment = MkEnvironment
  { prdEnv :: Map FreeVarName (Term Prd, Loc, TypeScheme Pos)
  , cnsEnv :: Map FreeVarName (Term Cns, Loc, TypeScheme Neg)
  , cmdEnv :: Map FreeVarName (Command, Loc)
  , classEnv :: Map ClassName ClassDeclaration
  , instanceDeclEnv :: Map FreeVarName InstanceDeclaration
  , instanceEnv :: Map ClassName (Set (FreeVarName, Typ Pos, Typ Neg))
  , declEnv :: [(Loc,DataDecl)]
  , kindEnv :: Map XtorName EvaluationOrder -- for each xtructor a return kind 
  , xtorEnv :: Map XtorName StructuralXtorDeclaration
  }

emptyEnvironment :: Environment
emptyEnvironment = MkEnvironment M.empty M.empty M.empty M.empty M.empty M.empty [] M.empty M.empty
instance Show Environment where
  show _ = "<Environment>"
