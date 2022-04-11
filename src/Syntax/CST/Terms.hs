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


data TermOrStar where
    ToSTerm :: Term -> TermOrStar
    ToSStar :: TermOrStar

deriving instance Show TermOrStar
deriving instance Eq TermOrStar

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

data FVOrStar where
    FoSFV :: FreeVarName -> FVOrStar
    FoSStar :: FVOrStar

deriving instance Show FVOrStar
deriving instance Eq FVOrStar

type BindingSite = [FVOrStar]

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


--------------------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------------------


data PrimCommand where
  -- AST Nodes
  Print :: Loc -> Term -> Term -> PrimCommand
  Read  :: Loc -> Term -> PrimCommand
  ExitSuccess  :: Loc -> PrimCommand
  ExitFailure :: Loc -> PrimCommand
  PrimOp :: Loc -> PrimitiveType -> PrimitiveOp -> [Term] -> PrimCommand
  -- Sugar Nodes

deriving instance Show PrimCommand
deriving instance Eq PrimCommand

getLocPC :: PrimCommand -> Loc 
getLocPC (Print loc _ _) = loc 
getLocPC (Read loc _) = loc 
getLocPC (ExitSuccess loc) = loc 
getLocPC (ExitFailure loc) = loc 
getLocPC (PrimOp loc _ _ _) = loc

data Term where
    PrimCmdTerm :: PrimCommand -> Term 
    Var :: Loc -> FreeVarName -> Term
    XtorSemi :: Loc -> XtorName -> [Term] -> Maybe Term -> Term
    XCase :: Loc -> DataCodata -> Maybe Term -> [TermCase] -> Term    
    MuAbs :: Loc -> FreeVarName -> Term -> Term
    Dtor :: Loc -> XtorName -> Term -> [TermOrStar] -> Term
    PrimLitI64 :: Loc -> Integer -> Term
    PrimLitF64 :: Loc -> Double -> Term
    DtorChain :: SourcePos -> Term -> NonEmpty (XtorName, [TermOrStar], SourcePos) -> Term
    NatLit :: Loc -> NominalStructural -> Int -> Term
    TermParens :: Loc -> Term -> Term
    FunApp :: Loc -> Term -> Term -> Term
    MultiLambda :: Loc -> [FreeVarName] -> Term -> Term
    Lambda :: Loc -> FreeVarName -> Term -> Term
    Apply :: Loc -> Term -> Term -> Term 



deriving instance Show Term
deriving instance Eq Term

getLoc :: Term -> Loc
getLoc (Var loc _) = loc
getLoc (XtorSemi loc _ _ _) = loc
getLoc (MuAbs loc _ _) = loc
getLoc (Dtor loc _ _ _) = loc
getLoc (XCase loc _ _ _) = loc
getLoc (PrimLitI64 loc _) = loc
getLoc (PrimLitF64 loc _) = loc
getLoc (DtorChain _ tm _)  = getLoc tm
getLoc (NatLit loc _ _) = loc
getLoc (TermParens loc _) = loc
getLoc (FunApp loc _ _) = loc
getLoc (MultiLambda loc _ _) = loc
getLoc (Lambda loc _ _) = loc
getLoc (Apply loc _ _) = loc 
getLoc (PrimCmdTerm pc) = getLocPC pc 
