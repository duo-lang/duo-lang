module Syntax.CST.Terms where

import Data.List.NonEmpty (NonEmpty(..))
import Text.Megaparsec.Pos (SourcePos)

import Syntax.CommonTerm
import Utils

--------------------------------------------------------------------------------------------
-- Substitutions and Binding Sites
--------------------------------------------------------------------------------------------

data PrdCnsTerm where
    PrdTerm :: Term -> PrdCnsTerm
    CnsTerm :: Term -> PrdCnsTerm

deriving instance Show PrdCnsTerm
deriving instance Eq PrdCnsTerm

type Substitution = [PrdCnsTerm]
type SubstitutionI = (Substitution,PrdCns,Substitution)

type BindingSite = [(PrdCns,FreeVarName)]
type BindingSiteI = (BindingSite, (), BindingSite)

--------------------------------------------------------------------------------------------
-- Cases/Cocases
--------------------------------------------------------------------------------------------

type CommandCase = (Loc, Bool, XtorName', BindingSite,  Command)
type TermCase    = (Loc, Bool, XtorName', BindingSite,  Term)
type TermCaseI   = (Loc, Bool, XtorName', BindingSiteI, Term)

--------------------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------------------

data Term where
    -- AST Nodes
    Var :: Loc -> FreeVarName -> Term
    Xtor :: Loc -> Bool -> XtorName' -> Substitution -> Term
    XMatch :: Loc -> [CommandCase] -> Term
    MuAbs :: Loc -> FreeVarName -> Command -> Term
    Dtor :: Loc -> Bool -> XtorName' -> Term -> SubstitutionI -> Term
    Case :: Loc -> Term -> [TermCase] -> Term
    Cocase :: Loc -> [TermCaseI] -> Term
    -- Sugar Nodes
    DtorChain :: SourcePos -> Term -> NonEmpty (Bool, XtorName', SubstitutionI, SourcePos) -> Term
    NatLit :: Loc -> NominalStructural -> Int -> Term
    TermParens :: Loc -> Term -> Term
    FunApp :: Loc -> Term -> Term -> Term
    MultiLambda :: Loc -> [FreeVarName] -> Term -> Term
    Lambda :: Loc -> FreeVarName -> Term -> Term

deriving instance Show Term
deriving instance Eq Term

--------------------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------------------

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
