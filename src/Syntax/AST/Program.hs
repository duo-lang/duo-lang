module Syntax.AST.Program where

import Data.Kind (Type)  
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text (Text)

import Syntax.CommonTerm
    ( XtorName, FreeVarName, PrdCns(Cns, Prd), Phase(..), PrdCnsRep, ModuleName, NominalStructural)
import Syntax.AST.Terms( Command, Term )
import Syntax.AST.Types ( TypeScheme, DataCodata, Polarity(..), DataDecl, PrdCnsToPol )
import Syntax.CST.Program qualified as CST
import Syntax.Kinds (CallingConvention)
import Utils ( Loc )

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

type family DeclExt (ext :: Phase) :: Type where
  DeclExt Parsed = Loc
  DeclExt Inferred = Loc
  DeclExt Compiled = ()

data Declaration (ext :: Phase) where
  PrdCnsDecl     :: DeclExt ext -> PrdCnsRep pc -> CST.IsRec -> FreeVarName -> Maybe (TypeScheme (PrdCnsToPol pc)) -> Term pc ext -> Declaration ext
  CmdDecl        :: DeclExt ext -> FreeVarName -> Command ext                                                   -> Declaration ext
  DataDecl       :: DeclExt ext -> DataDecl                                                                     -> Declaration ext
  XtorDecl       :: DeclExt ext -> DataCodata -> XtorName -> [(PrdCns, CallingConvention)] -> CallingConvention -> Declaration ext
  ImportDecl     :: DeclExt ext -> ModuleName                                                                   -> Declaration ext
  SetDecl        :: DeclExt ext -> Text                                                                         -> Declaration ext
  

instance Show (Declaration ext) where
  show _ = "<Show for Declaration not implemented>"

type Program ext = [Declaration ext]

---------------------------------------------------------------------------------
-- Environment
---------------------------------------------------------------------------------

data Environment (ph :: Phase) = MkEnvironment
  { prdEnv :: Map FreeVarName (Term Prd ph, Loc, TypeScheme Pos)
  , cnsEnv :: Map FreeVarName (Term Cns ph, Loc, TypeScheme Neg)
  , cmdEnv :: Map FreeVarName (Command ph, Loc)
  , declEnv :: [(Loc,DataDecl)]
  , xtorMap :: Map XtorName NominalStructural
  }

instance Show (Environment ph) where
  show _ = "<Environment>"

instance Semigroup (Environment ph) where
  (MkEnvironment prdEnv1 cnsEnv1 cmdEnv1 declEnv1 xtorMap1) <> (MkEnvironment prdEnv2 cnsEnv2 cmdEnv2 declEnv2 xtorMap2) =
    MkEnvironment { prdEnv = M.union prdEnv1 prdEnv2
                  , cnsEnv = M.union cnsEnv1 cnsEnv2
                  , cmdEnv = M.union cmdEnv1 cmdEnv2
                  , declEnv = declEnv1 ++ declEnv2
                  , xtorMap = M.union xtorMap1 xtorMap2
                  }

instance Monoid (Environment ph) where
  mempty = MkEnvironment
    { prdEnv = M.empty
    , cnsEnv = M.empty
    , cmdEnv = M.empty
    , declEnv = []
    , xtorMap = M.empty
    }
