module Syntax.CST.Terms where

import Data.List.NonEmpty (NonEmpty(..))
import Text.Megaparsec.Pos (SourcePos)

import Syntax.Common
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

substitutionToArity :: Substitution -> Arity
substitutionToArity = map f
  where
    f (PrdTerm _) = Prd
    f (CnsTerm _) = Cns

substitutionIToArity :: SubstitutionI -> Arity
substitutionIToArity (subst1, pc, subst2) =
  substitutionToArity subst1 ++ [case pc of Prd -> Cns; Cns -> Prd] ++ substitutionToArity subst2

type BindingSite = [(PrdCns,FreeVarName)]
type BindingSiteI = (BindingSite, (), BindingSite)

--------------------------------------------------------------------------------------------
-- Cases/Cocases
--------------------------------------------------------------------------------------------

data TermCase  = MkTermCase
  { tmcase_ext  :: Loc
  , tmcase_name :: XtorName
  , tmcase_args :: BindingSite
  , tmcase_term :: Term
  }

deriving instance Show TermCase
deriving instance Eq TermCase

data TermCaseI = MkTermCaseI
  { tmcasei_ext  :: Loc
  , tmcasei_name :: XtorName
  , tmcasei_args :: BindingSiteI
  , tmcasei_term :: Term
  }

deriving instance Show TermCaseI
deriving instance Eq TermCaseI

data CmdCase = MkCmdCase
  { cmdcase_ext  :: Loc
  , cmdcase_name :: XtorName
  , cmdcase_args :: BindingSite
  , cmdcase_cmd  :: Command
  }

deriving instance Show CmdCase
deriving instance Eq CmdCase

--------------------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------------------

data Term where
    -- AST Nodes
    Var :: Loc -> FreeVarName -> Term
    Xtor :: Loc -> XtorName -> Substitution -> Term
    XMatch :: Loc -> DataCodata -> [CmdCase] -> Term
    MuAbs :: Loc -> FreeVarName -> Command -> Term
    Dtor :: Loc -> XtorName -> Term -> SubstitutionI -> Term
    Case :: Loc -> Term -> [TermCase] -> Term
    Cocase :: Loc -> [TermCaseI] -> Term
    PrimLitI64 :: Loc -> Integer -> Term
    PrimLitF64 :: Loc -> Double -> Term
    -- Sugar Nodes
    DtorChain :: SourcePos -> Term -> NonEmpty (XtorName, SubstitutionI, SourcePos) -> Term
    NatLit :: Loc -> NominalStructural -> Int -> Term
    TermParens :: Loc -> Term -> Term
    FunApp :: Loc -> Term -> Term -> Term
    MultiLambda :: Loc -> [FreeVarName] -> Term -> Term
    Lambda :: Loc -> FreeVarName -> Term -> Term
    --CaseCnsI :: Loc -> [TermCaseI] -> Term
    --Semicolon :: Loc -> XtorName -> SubstitutionI -> Term -> Term 
    --CocaseCns :: Loc -> Term -> [TermCaseI] -> Term



deriving instance Show Term
deriving instance Eq Term

getLoc :: Term -> Loc
getLoc (Var loc _) = loc
getLoc (Xtor loc _ _) = loc
getLoc (XMatch loc _ _) = loc
getLoc (MuAbs loc _ _) = loc
getLoc (Dtor loc _ _ _) = loc
getLoc (Case loc _ _) = loc
getLoc (Cocase loc _) = loc
getLoc (PrimLitI64 loc _) = loc
getLoc (PrimLitF64 loc _) = loc
getLoc (DtorChain _ tm _)  = getLoc tm
getLoc (NatLit loc _ _) = loc
getLoc (TermParens loc _) = loc
getLoc (FunApp loc _ _) = loc
getLoc (MultiLambda loc _ _) = loc
getLoc (Lambda loc _ _) = loc
--getLoc (CaseCnsI loc _ ) = loc 
--getLoc (Semicolon loc _ _ _ ) = loc 
--getLoc (CocaseCns loc _ _ ) = loc 

--------------------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------------------

data Command where
  -- AST Nodes
  Apply :: Loc -> Term -> Term -> Command
  Print :: Loc -> Term -> Command -> Command
  Read  :: Loc -> Term -> Command
  Jump  :: Loc -> FreeVarName -> Command
  ExitSuccess  :: Loc -> Command
  ExitFailure :: Loc -> Command
  PrimOp :: Loc -> PrimitiveType -> PrimitiveOp -> Substitution -> Command
  -- Sugar Nodes
  CommandParens :: Loc -> Command -> Command

deriving instance Show Command
deriving instance Eq Command
