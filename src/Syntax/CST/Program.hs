module Syntax.CST.Program where

import Data.Text (Text)

import Syntax.CST.Terms
import Syntax.CST.Types
import Syntax.CommonTerm
import Syntax.Lowering.Types (Assoc(..))
import Utils

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data IsRec = Recursive | NonRecursive

data Declaration where
  PrdCnsDecl     :: Loc -> PrdCns-> IsRec -> FreeVarName -> Maybe TypeScheme -> Term             -> Declaration
  CmdDecl        :: Loc -> FreeVarName -> Command                                                -> Declaration
  DataDecl       :: Loc -> DataDecl                                                              -> Declaration
  ImportDecl     :: Loc -> ModuleName                                                            -> Declaration
  SetDecl        :: Loc -> Text                                                                  -> Declaration
  FixityDecl     :: Loc -> Assoc                                                                 -> Declaration
  ParseErrorDecl ::                                                                                 Declaration

instance Show Declaration where
  show _ = "<Show for Declaration not implemented>"

type Program = [Declaration]