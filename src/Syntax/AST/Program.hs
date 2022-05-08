{-# LANGUAGE UndecidableInstances #-}
module Syntax.AST.Program where

import Data.Text (Text)

import Syntax.Common
import Syntax.AST.Terms( Command, Term )
import Syntax.Common.TypesPol ( DataDecl, TopAnnot, Typ )
import Utils ( Loc )

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data Declaration where
  PrdCnsDecl     :: Loc -> Maybe DocComment -> PrdCnsRep pc -> IsRec -> FreeVarName -> TopAnnot (PrdCnsToPol pc) -> Term pc -> Declaration
  CmdDecl        :: Loc -> Maybe DocComment -> FreeVarName -> Command                                                       -> Declaration
  DataDecl       :: Loc -> Maybe DocComment -> DataDecl                                                                     -> Declaration
  XtorDecl       :: Loc -> Maybe DocComment -> DataCodata -> XtorName -> [(PrdCns, MonoKind)] -> EvaluationOrder            -> Declaration
  ImportDecl     :: Loc -> Maybe DocComment -> ModuleName                                                                   -> Declaration
  SetDecl        :: Loc -> Maybe DocComment -> Text                                                                         -> Declaration
  TyOpDecl       :: Loc -> Maybe DocComment -> TyOpName -> Precedence -> Associativity -> RnTypeName                        -> Declaration
  TySynDecl      :: Loc -> Maybe DocComment -> TypeName -> (Typ Pos, Typ Neg)                                               -> Declaration
  

instance Show Declaration where
  show (PrdCnsDecl loc doc PrdRep isrec fv annot tm) = "PrdDecl: " ++ show loc ++ show doc ++ show isrec ++ show fv ++ show annot ++ show tm
  show (PrdCnsDecl loc doc CnsRep isrec fv annot tm) = "CnsDecl: " ++ show loc ++ show doc ++ show isrec ++ show fv ++ show annot ++ show tm
  show (CmdDecl loc doc fv cmd) = "CmdDecl: " ++ show loc ++ show doc ++ show fv ++ show cmd
  show (DataDecl loc doc dcl)= "DataDecl: " ++ show loc ++ show doc ++ show dcl
  show (XtorDecl loc doc dc xt args res) = "XtorDecl: " ++ show loc ++ show doc ++ show dc ++ show xt ++ show args ++ show res
  show (ImportDecl loc doc mn) = "ImportDecl: " ++ show loc ++ show doc ++ show mn
  show (SetDecl loc doc txt) = "SetDecl: " ++ show loc ++ show doc ++ show txt
  show (TyOpDecl loc doc op prec assoc ty) = "TyOpDecl: " ++ show loc ++ show doc ++ show op ++ show prec ++ show assoc ++ show ty
  show (TySynDecl loc doc nm ty) = "TySynDecl: " ++ show loc ++ show doc ++ show nm ++ show ty
  
type Program = [Declaration]