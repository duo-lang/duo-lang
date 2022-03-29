module Syntax.CST.Program where

import Data.Text (Text)

import Syntax.CST.Terms
import Syntax.CST.Types
import Syntax.Common
import Utils

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data Declaration where
  PrdCnsDecl     :: Maybe DocComment -> Loc -> PrdCns-> IsRec -> FreeVarName -> Maybe TypeScheme -> Term                    -> Declaration
  CmdDecl        :: Maybe DocComment -> Loc -> FreeVarName -> Command                                                       -> Declaration
  DataDecl       :: Maybe DocComment -> Loc -> DataDecl                                                                     -> Declaration
  XtorDecl       :: Maybe DocComment -> Loc -> DataCodata -> XtorName -> [(PrdCns, MonoKind)] -> Maybe EvaluationOrder      -> Declaration
  ImportDecl     :: Maybe DocComment -> Loc -> ModuleName                                                                   -> Declaration
  SetDecl        :: Maybe DocComment -> Loc -> Text                                                                         -> Declaration
  TyOpDecl       :: Maybe DocComment -> Loc -> TyOpName -> Precedence -> Associativity -> TypeName                          -> Declaration
  ParseErrorDecl ::                                                                                                            Declaration

instance Show Declaration where
  show _ = "<Show for Declaration not implemented>"

type Program = [Declaration]