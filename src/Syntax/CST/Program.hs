module Syntax.CST.Program where

import Data.Text (Text)

import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.AST.Types
import Syntax.CommonTerm
import Utils
---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data IsRec = Recursive | NonRecursive

data Declaration where
  PrdCnsDecl     :: Loc -> PrdCns-> IsRec -> FreeVarName -> Maybe CST.TypeScheme -> CST.Term     -> Declaration
  CmdDecl        :: Loc -> FreeVarName -> CST.Command                                            -> Declaration
  DataDecl       :: Loc -> DataDecl                                                              -> Declaration
  ImportDecl     :: Loc -> ModuleName                                                            -> Declaration
  SetDecl        :: Loc -> Text                                                                  -> Declaration
  ParseErrorDecl ::                                                                                 Declaration

instance Show Declaration where
  show _ = "<Show for Declaration not implemented>"

type Program = [Declaration]