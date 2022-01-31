module Syntax.CST.Program where

import Data.Text (Text)

import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.Types
import Syntax.CommonTerm
import Utils
---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

newtype ModuleName = ModuleName { unModuleName :: Text }

data IsRec = Recursive | NonRecursive

data Declaration where
  PrdCnsDecl     :: Loc -> PrdCns-> IsRec -> FreeVarName -> Maybe CST.TypeScheme -> CST.Term -> Declaration
  CmdDecl        :: Loc -> FreeVarName -> CST.Command                                        -> Declaration
  DataDecl       :: Loc -> DataDecl                                                          -> Declaration
  ImportDecl     :: Loc -> ModuleName                                                        -> Declaration
  SetDecl        :: Loc -> Text                                                              -> Declaration
  ParseErrorDecl ::                                                                             Declaration

type Program = [Declaration]