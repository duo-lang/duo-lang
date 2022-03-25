{-# LANGUAGE UndecidableInstances #-}
module Syntax.AST.Program where

import Data.Kind (Type)  
import Data.Text (Text)

import Syntax.Common
import Syntax.AST.Terms( Command, Term )
import Syntax.AST.Types ( TypeScheme, DataDecl )
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
  XtorDecl       :: DeclExt ext -> DataCodata -> XtorName -> [(PrdCns, CallingConvention)] -> EvaluationOrder   -> Declaration ext
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