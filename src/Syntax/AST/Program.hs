{-# LANGUAGE UndecidableInstances #-}
module Syntax.AST.Program where

import Data.Kind (Type)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text (Text)

import Syntax.Common
import Syntax.AST.Terms( Command, Term )
import Syntax.AST.Types ( TypeScheme, DataDecl )
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
  PrdCnsDecl     :: DeclExt ext -> PrdCnsRep pc -> IsRec -> FreeVarName -> Maybe (TypeScheme (PrdCnsToPol pc)) -> Term pc ext -> Declaration ext
  CmdDecl        :: DeclExt ext -> FreeVarName -> Command ext                                                   -> Declaration ext
  DataDecl       :: DeclExt ext -> DataDecl                                                                     -> Declaration ext
  XtorDecl       :: DeclExt ext -> DataCodata -> XtorName -> [(PrdCns, CallingConvention)] -> CallingConvention -> Declaration ext
  ImportDecl     :: DeclExt ext -> ModuleName                                                                   -> Declaration ext
  SetDecl        :: DeclExt ext -> Text                                                                         -> Declaration ext


instance (Show (DeclExt ext), Show (Term Prd ext), Show (Term Cns ext), Show (Command ext)) => Show (Declaration ext) where
  show (PrdCnsDecl ext PrdRep isrec fv annot tm) = "PrdDecl: " ++ show ext ++ show isrec ++ show fv ++ show annot ++ show tm
  show (PrdCnsDecl ext CnsRep isrec fv annot tm) = "CnsDecl: " ++ show ext ++ show isrec ++ show fv ++ show annot ++ show tm
  show (CmdDecl ext fv cmd) = "CmdDecl: " ++ show ext ++ show fv ++ show cmd
  show (DataDecl ext dcl)= "DataDecl: " ++ show ext ++ show dcl
  show (XtorDecl ext dc xt args res) = "XtorDecl: " ++ show ext ++ show dc ++ show xt ++ show args ++ show res
  show (ImportDecl ext mn) = "ImportDecl: " ++ show ext ++ show mn
  show (SetDecl ext txt) = "SetDecl: " ++ show ext ++ show txt

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
