module Syntax.Program where

import Data.Kind (Type)  
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text (Text)

import Syntax.CommonTerm
    ( FreeVarName, PrdCns(Cns, Prd), Phase(..), PrdCnsRep )
import Syntax.STerms( Command, STerm )
import Syntax.ATerms ( ATerm )
import Syntax.Types ( TypeScheme, Polarity(..), DataDecl, PrdCnsToPol )
import Utils ( Loc )

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

type family DeclExt (ext :: Phase) :: Type where
  DeclExt Parsed = Loc
  DeclExt Inferred = Loc
  DeclExt Compiled = ()

newtype ModuleName = ModuleName { unModuleName :: Text }
data IsRec = Recursive | NonRecursive

data Declaration (ext :: Phase) where
  PrdCnsDecl     :: DeclExt ext -> PrdCnsRep pc -> IsRec -> FreeVarName -> Maybe (TypeScheme (PrdCnsToPol pc)) -> STerm pc ext -> Declaration ext
  CmdDecl        :: DeclExt ext -> FreeVarName -> Command ext                                      -> Declaration ext
  DataDecl       :: DeclExt ext -> DataDecl                                                        -> Declaration ext
  ImportDecl     :: DeclExt ext -> ModuleName                                                      -> Declaration ext
  SetDecl        :: DeclExt ext -> Text                                                            -> Declaration ext
  ParseErrorDecl ::                                                                                   Declaration ext


instance Show (Declaration ext) where
  show _ = "<Show for Declaration not implemented>"

type Program ext = [Declaration ext]

---------------------------------------------------------------------------------
-- Environment
---------------------------------------------------------------------------------

data Environment = Environment
  { prdEnv :: Map FreeVarName (STerm Prd Inferred, Loc, TypeScheme Pos)
  , cnsEnv :: Map FreeVarName (STerm Cns Inferred, Loc, TypeScheme Neg)
  , cmdEnv :: Map FreeVarName (Command Inferred, Loc)
  , declEnv :: [(Loc,DataDecl)]
  }

instance Show Environment where
  show _ = "<Environment>"

instance Semigroup Environment where
  (Environment prdEnv1 cnsEnv1 cmdEnv1 declEnv1) <> (Environment prdEnv2 cnsEnv2 cmdEnv2 declEnv2) =
    Environment { prdEnv = M.union prdEnv1 prdEnv2
                , cnsEnv = M.union cnsEnv1 cnsEnv2
                , cmdEnv = M.union cmdEnv1 cmdEnv2
                , declEnv = declEnv1 ++ declEnv2
                }

instance Monoid Environment where
  mempty = Environment
    { prdEnv = M.empty
    , cnsEnv = M.empty
    , cmdEnv = M.empty
    , declEnv = []
    }
