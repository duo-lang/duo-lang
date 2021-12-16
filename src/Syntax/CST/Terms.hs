module Syntax.CST.Terms where

import Syntax.CommonTerm
import Utils

data PrdCnsTerm where
    PrdTerm :: Term -> PrdCnsTerm
    CnsTerm :: Term -> PrdCnsTerm

type Substitution = [PrdCnsTerm]
type SubstitutionI = ([PrdCnsTerm],PrdCns,[PrdCnsTerm])

type TermCase = (XtorName, [(PrdCns,FreeVarName)], Term)
type TermCaseI = (XtorName, ([(PrdCns, FreeVarName)],(),[FreeVarName]), Term)
type CommandCase = (XtorName, [(PrdCns, FreeVarName)], Command)

data Term where
    -- AST Nodes
    Var :: Loc -> FreeVarName -> Term
    XtorCall :: Loc -> XtorName -> Substitution -> Term
    XMatch :: Loc -> [()] -> Term
    MuAbs :: Loc -> FreeVarName -> Command -> Term
    Dtor :: Loc -> XtorName -> Term -> SubstitutionI -> Term
    Match :: Loc -> Term -> [TermCase] -> Term
    Comatch :: Loc -> [TermCaseI] -> Term
    -- Sugar Nodes
    NatLit :: Loc -> Int -> Term
    TermParens :: Loc -> Term -> Term
    FunApp :: Loc -> Term -> Term -> Term
    Lambda :: Loc -> FreeVarName -> Term -> Term


data Command where
  -- AST Nodes
  Apply :: Loc -> Term -> Term -> Command
  Print :: Loc -> Term -> Command -> Command
  Read  :: Loc -> Term -> Command
  Call  :: Loc -> FreeVarName -> Command
  Done  :: Loc -> Command
  -- Sugar Nodes
  CommandParens :: Loc -> Command -> Command
