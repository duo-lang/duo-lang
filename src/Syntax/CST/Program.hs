module Syntax.CST.Program where

import Data.Text (Text)

import Syntax.AST.Types (TVar)
import Syntax.CST.Terms
import Syntax.CST.Types
import Syntax.Common
import Syntax.Lowering.Types (Assoc, Precedence, Variance)
import Utils

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data Declaration where
  PrdCnsDecl     :: Loc -> PrdCns-> IsRec -> FreeVarName -> Maybe TypeScheme -> Term             -> Declaration
  CmdDecl        :: Loc -> FreeVarName -> Command                                                -> Declaration
  DataDecl       :: Loc -> DataDecl                                                              -> Declaration
  ImportDecl     :: Loc -> ModuleName                                                            -> Declaration
  SetDecl        :: Loc -> Text                                                                  -> Declaration
  FixityDecl     :: Loc -> Assoc -> Precedence -> ((Variance,TVar), BinOp, (Variance,TVar)) -> Typ                     -> Declaration
  ParseErrorDecl ::                                                                                 Declaration

instance Show Declaration where
  show _ = "<Show for Declaration not implemented>"

type Program = [Declaration]