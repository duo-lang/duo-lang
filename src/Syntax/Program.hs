module Syntax.Program where
  
import Data.Bifunctor ( Bifunctor(bimap) )
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

data Declaration a b
  = PrdDecl IsRec b FreeVarName (Maybe (TypeScheme Pos)) (STerm Prd b a)
  | CnsDecl IsRec b FreeVarName (Maybe (TypeScheme Neg)) (STerm Cns b a)
  | CmdDecl b FreeVarName (Command b a)
  | DefDecl IsRec b FreeVarName (Maybe (TypeScheme Pos)) (ATerm b a)
  | DataDecl b DataDecl
  | ImportDecl b ModuleName
  | ParseErrorDecl

instance Show (Declaration a b) where
  show _ = "<Show for Declaration not implemented>"

instance Bifunctor Declaration where
  bimap f g (PrdDecl isRec b v ts t) = PrdDecl isRec (g b) v ts $ bimap g f t
  bimap f g (CnsDecl isRec b v ts t) = CnsDecl isRec (g b) v ts $ bimap g f t
  bimap f g (CmdDecl b v cmd) = CmdDecl (g b) v $ bimap g f cmd
  bimap f g (DefDecl isRec b v ts t) = DefDecl isRec (g b) v ts $ bimap g f t
  bimap _ g (DataDecl b dataDecl) = DataDecl (g b) dataDecl
  bimap _ g (ImportDecl b mod) = ImportDecl (g b) mod
  bimap _ _ ParseErrorDecl = ParseErrorDecl

type Program a b = [Declaration a b]

---------------------------------------------------------------------------------
-- Environment
---------------------------------------------------------------------------------

data Environment bs = Environment
  { prdEnv :: Map FreeVarName (STerm Prd () bs, Loc, TypeScheme Pos)
  , cnsEnv :: Map FreeVarName (STerm Cns () bs, Loc, TypeScheme Neg)
  , cmdEnv :: Map FreeVarName (Command () bs, Loc)
  , defEnv :: Map FreeVarName (ATerm () bs, Loc,  TypeScheme Pos)
  , declEnv :: [DataDecl]
  }

instance Show (Environment bs) where
  show _ = "<Environment>"

instance Semigroup (Environment bs) where
  (Environment prdEnv1 cnsEnv1 cmdEnv1 defEnv1 declEnv1) <> (Environment prdEnv2 cnsEnv2 cmdEnv2 defEnv2 declEnv2) =
    Environment { prdEnv = M.union prdEnv1 prdEnv2
                , cnsEnv = M.union cnsEnv1 cnsEnv2
                , cmdEnv = M.union cmdEnv1 cmdEnv2
                , defEnv = M.union defEnv1 defEnv2
                , declEnv = declEnv1 ++ declEnv2
                }

instance Monoid (Environment bs) where
  mempty = Environment
    { prdEnv = M.empty
    , cnsEnv = M.empty
    , cmdEnv = M.empty
    , defEnv = M.empty
    , declEnv = []
    }
