module Syntax.CST.Program where

import Data.Text (Text)

import Syntax.CST.Terms
import Syntax.Common.TypesUnpol
import Syntax.Common
import Utils

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data Declaration where 
  PrdCnsDecl     :: Loc -> Maybe DocComment -> PrdCns-> IsRec -> FreeVarName -> Maybe TypeScheme -> Term                    -> Declaration
  CmdDecl        :: Loc -> Maybe DocComment -> FreeVarName -> Term                                                          -> Declaration
  DataDecl       :: Loc -> Maybe DocComment -> DataDecl                                                                     -> Declaration
  XtorDecl       :: Loc -> Maybe DocComment -> DataCodata -> XtorName -> [(PrdCns, MonoKind)] -> Maybe EvaluationOrder      -> Declaration
  ImportDecl     :: Loc -> Maybe DocComment -> ModuleName                                                                   -> Declaration
  SetDecl        :: Loc -> Maybe DocComment -> Text                                                                         -> Declaration
  TyOpDecl       :: Loc -> Maybe DocComment -> TyOpName -> Precedence -> Associativity -> TypeName                          -> Declaration
  TySynDecl      :: Loc -> Maybe DocComment -> TypeName -> Typ                                                              -> Declaration
  ClassDecl      :: Loc -> Maybe DocComment -> ClassName -> [(Variance, TVar, MonoKind)] -> [(XtorName, [(PrdCns, Typ)])]   -> Declaration
  InstanceDecl   :: Loc -> Maybe DocComment -> ClassName -> Typ -> [TermCase]                                               -> Declaration
  ParseErrorDecl ::                                                                                                            Declaration

instance Show Declaration where
  show _ = "<Show for Declaration not implemented>"

type Program = [Declaration]