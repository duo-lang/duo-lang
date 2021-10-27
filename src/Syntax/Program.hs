module Syntax.Program where
  
import Data.Map (Map)
import qualified Data.Map as M
import Data.Text (Text)
import Syntax.STerms( PrdCns(..), Command, STerm, FreeVarName )
import Syntax.ATerms ( ATerm )
import Syntax.Types ( TypeScheme, Polarity(..), DataDecl )
import Utils ( Loc )

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

newtype ModuleName = ModuleName { unModuleName :: Text }
data IsRec = Recursive | NonRecursive

data Declaration ext
  = PrdDecl IsRec ext FreeVarName (Maybe (TypeScheme Pos)) (STerm Prd ext)
  | CnsDecl IsRec ext FreeVarName (Maybe (TypeScheme Neg)) (STerm Cns ext)
  | CmdDecl ext FreeVarName (Command ext)
  | DefDecl IsRec ext FreeVarName (Maybe (TypeScheme Pos)) (ATerm ext)
  | DataDecl ext DataDecl
  | ImportDecl ext ModuleName
  | SetDecl ext Text
  | ParseErrorDecl
  deriving (Functor)

instance Show (Declaration ext) where
  show _ = "<Show for Declaration not implemented>"

type Program ext = [Declaration ext]

---------------------------------------------------------------------------------
-- Environment
---------------------------------------------------------------------------------

data Environment = Environment
  { prdEnv :: Map FreeVarName (STerm Prd (), Loc, TypeScheme Pos)
  , cnsEnv :: Map FreeVarName (STerm Cns (), Loc, TypeScheme Neg)
  , cmdEnv :: Map FreeVarName (Command (), Loc)
  , defEnv :: Map FreeVarName (ATerm (), Loc,  TypeScheme Pos)
  , declEnv :: [(Loc,DataDecl)]
  }

instance Show Environment where
  show _ = "<Environment>"

instance Semigroup Environment where
  (Environment prdEnv1 cnsEnv1 cmdEnv1 defEnv1 declEnv1) <> (Environment prdEnv2 cnsEnv2 cmdEnv2 defEnv2 declEnv2) =
    Environment { prdEnv = M.union prdEnv1 prdEnv2
                , cnsEnv = M.union cnsEnv1 cnsEnv2
                , cmdEnv = M.union cmdEnv1 cmdEnv2
                , defEnv = M.union defEnv1 defEnv2
                , declEnv = declEnv1 ++ declEnv2
                }

instance Monoid Environment where
  mempty = Environment
    { prdEnv = M.empty
    , cnsEnv = M.empty
    , cmdEnv = M.empty
    , defEnv = M.empty
    , declEnv = []
    }
