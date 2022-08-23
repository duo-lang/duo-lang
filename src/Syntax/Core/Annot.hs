module Syntax.Core.Annot where

import Syntax.CST.Types ( PrdCnsRep, PrdCns )

data MuAnnot where
  -- | User-written Mu abstraction
  MuAnnotOrig :: MuAnnot
  -- Semi/Dtor
  MuAnnotSemi :: MuAnnot
  MuAnnotDtor :: MuAnnot
  -- CaseOf / CocaseOf
  MuAnnotCaseOf :: MuAnnot
  MuAnnotCocaseOf :: MuAnnot
  deriving (Ord, Eq, Show)

data MatchAnnot (pc :: PrdCns) where
  -- | User-written XCase abstraction
  MatchAnnotOrig :: MatchAnnot pc
  -- CaseOf / CocaseOf
  MatchAnnotCaseOf :: MatchAnnot pc 
  MatchAnnotCocaseOf :: MatchAnnot pc 
  -- CaseI / CocaseI
  MatchAnnotXCaseI :: PrdCnsRep pc -> MatchAnnot pc 
  -- CaseOfI / CocaseOfI
  MatchAnnotCaseOfI :: MatchAnnot pc 
  MatchAnnotCocaseOfI :: MatchAnnot pc 
  -- CaseOfCmd / CocaseOfCmd
  MatchAnnotCaseOfCmd :: MatchAnnot pc 
  MatchAnnotCocaseOfCmd :: MatchAnnot pc 
  -- Lambda / Colambda
  MatchAnnotLambda :: MatchAnnot pc 
  deriving (Eq, Show)

data XtorAnnot where
  -- | User-written XCase abstraction
  XtorAnnotOrig :: XtorAnnot
  -- Semi/Dtor
  XtorAnnotSemi :: Int -> XtorAnnot
  XtorAnnotDtor :: Int -> XtorAnnot
  deriving (Ord, Eq, Show)

data ApplyAnnot where
  -- User-written apply command
  ApplyAnnotOrig :: ApplyAnnot
  -- Semi/Dtor
  ApplyAnnotSemi :: ApplyAnnot
  ApplyAnnotDtor :: ApplyAnnot
  -- CaseOf/CocaseOf
  ApplyAnnotCaseOfInner :: ApplyAnnot
  ApplyAnnotCaseOfOuter :: ApplyAnnot
  ApplyAnnotCocaseOfInner :: ApplyAnnot
  ApplyAnnotCocaseOfOuter :: ApplyAnnot
  -- CaseI/CocaseI
  ApplyAnnotXCaseI :: Int -> ApplyAnnot
    -- CaseOfCmd/CocaseOfCmd
  ApplyAnnotCaseOfCmd :: ApplyAnnot
  ApplyAnnotCocaseOfCmd :: ApplyAnnot
  -- CaseOfI/CocaseOfI
  ApplyAnnotXCaseOfIInner :: Int -> ApplyAnnot
  ApplyAnnotCaseOfIOuter :: ApplyAnnot
  ApplyAnnotCocaseOfIOuter :: ApplyAnnot

  ApplyAnnotLambda :: ApplyAnnot
  deriving (Ord, Eq, Show)

    