module Syntax.CST.Terms where

import Data.List.NonEmpty (NonEmpty(..))
import Text.Megaparsec.Pos (SourcePos)

import Syntax.Common
import Utils

--------------------------------------------------------------------------------------------
-- Substitutions and Binding Sites
--------------------------------------------------------------------------------------------

data TermOrStar where
    ToSTerm :: Term -> TermOrStar
    ToSStar :: TermOrStar

deriving instance Show TermOrStar
deriving instance Eq TermOrStar

type Substitution = [Term]
type SubstitutionI = [TermOrStar]

data FVOrStar where
    FoSFV :: FreeVarName -> FVOrStar
    FoSStar :: FVOrStar

deriving instance Show FVOrStar
deriving instance Eq FVOrStar

isStar :: FVOrStar -> Bool
isStar FoSStar   = True
isStar (FoSFV _) = False

-- | Partial function!
fromFVOrStar :: FVOrStar -> FreeVarName
fromFVOrStar (FoSFV fv) = fv
fromFVOrStar FoSStar = error "fromFVOrStar called on FoSStar"


type BindingSite = [FVOrStar]

--------------------------------------------------------------------------------------------
-- Cases/Cocases
--------------------------------------------------------------------------------------------

data TermPat where
  XtorPat :: Loc -> XtorName -> BindingSite -> TermPat

deriving instance Show TermPat
deriving instance Eq TermPat

data TermCase  = MkTermCase
  { tmcase_loc  :: Loc
  , tmcase_pat  :: TermPat
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
    Xtor :: Loc -> XtorName -> SubstitutionI -> Term
    Semi :: Loc -> XtorName -> SubstitutionI -> Term -> Term
    Case :: Loc -> [TermCase] -> Term
    CaseOf :: Loc -> Term -> [TermCase] -> Term
    Cocase :: Loc -> [TermCase] -> Term
    CocaseOf :: Loc -> Term -> [TermCase] -> Term
    MuAbs :: Loc -> FreeVarName -> Term -> Term
    Dtor :: Loc -> XtorName -> Term -> SubstitutionI -> Term
    PrimLitI64 :: Loc -> Integer -> Term
    PrimLitF64 :: Loc -> Double -> Term
    DtorChain :: SourcePos -> Term -> NonEmpty (XtorName, SubstitutionI, SourcePos) -> Term
    NatLit :: Loc -> NominalStructural -> Int -> Term
    TermParens :: Loc -> Term -> Term
    FunApp :: Loc -> Term -> Term -> Term
    MultiLambda :: Loc -> [FreeVarName] -> Term -> Term
    MultiCoLambda :: Loc -> [FreeVarName] -> Term -> Term
    Lambda :: Loc -> FreeVarName -> Term -> Term
    Apply :: Loc -> Term -> Term -> Term 

deriving instance Show Term
deriving instance Eq Term

getLoc :: Term -> Loc
getLoc (Var loc _) = loc
getLoc (Xtor loc _ _) = loc
getLoc (Semi loc _ _ _) = loc
getLoc (MuAbs loc _ _) = loc
getLoc (Dtor loc _ _ _) = loc
getLoc (Case loc _) = loc
getLoc (CaseOf loc _ _) = loc
getLoc (Cocase loc _) = loc
getLoc (CocaseOf loc _ _) = loc
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
