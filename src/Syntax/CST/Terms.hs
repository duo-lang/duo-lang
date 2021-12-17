module Syntax.CST.Terms where

import Data.List.NonEmpty (NonEmpty(..))
import Text.Megaparsec.Pos (SourcePos)

import Syntax.CommonTerm
import Utils

data PrdCnsTerm where
    PrdTerm :: Term -> PrdCnsTerm
    CnsTerm :: Term -> PrdCnsTerm

deriving instance Show PrdCnsTerm
deriving instance Eq PrdCnsTerm

type Substitution = [PrdCnsTerm]
type SubstitutionI = ([PrdCnsTerm],PrdCns,[PrdCnsTerm])

type TermCase    = (Loc, XtorName, [(PrdCns,FreeVarName)],                     Term)
type TermCaseI   = (Loc, XtorName, ([(PrdCns, FreeVarName)],(),[(PrdCns,FreeVarName)]), Term)
type CommandCase = (Loc, XtorName, [(PrdCns, FreeVarName)],                    Command)

data Term where
    -- AST Nodes
    Var :: Loc -> FreeVarName -> Term
    Xtor :: Loc -> XtorName -> Substitution -> Term
    XMatch :: Loc -> [CommandCase] -> Term
    MuAbs :: Loc -> FreeVarName -> Command -> Term
    Dtor :: Loc -> XtorName -> Term -> SubstitutionI -> Term
    Case :: Loc -> Term -> [TermCase] -> Term
    Cocase :: Loc -> [TermCaseI] -> Term
    -- Sugar Nodes
    DtorChain :: SourcePos -> Term -> NonEmpty (XtorName, SubstitutionI, SourcePos) -> Term
    NatLit :: Loc -> NominalStructural -> Int -> Term
    TermParens :: Loc -> Term -> Term
    FunApp :: Loc -> Term -> Term -> Term
    Lambda :: Loc -> FreeVarName -> Term -> Term

deriving instance Show Term
deriving instance Eq Term

data Command where
  -- AST Nodes
  Apply :: Loc -> Term -> Term -> Command
  Print :: Loc -> Term -> Command -> Command
  Read  :: Loc -> Term -> Command
  Call  :: Loc -> FreeVarName -> Command
  Done  :: Loc -> Command
  -- Sugar Nodes
  CommandParens :: Loc -> Command -> Command

deriving instance Show Command
deriving instance Eq Command
