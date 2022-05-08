module Syntax.Common.Annot where

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

data MatchAnnot where
  -- | User-written XCase abstraction
  MatchAnnotOrig :: MatchAnnot
  -- CaseOf / CocaseOf
  MatchAnnotCaseOf :: MatchAnnot
  MatchAnnotCocaseOf :: MatchAnnot
  -- CaseI / CocaseI
  MatchAnnotCaseI :: MatchAnnot
  MatchAnnotCocaseI :: MatchAnnot
  -- CaseOfI / CocaseOfI
  MatchAnnotCaseOfI :: MatchAnnot
  MatchAnnotCocaseOfI :: MatchAnnot
  -- CaseOfCmd / CocaseOfCmd
  MatchAnnotCaseOfCmd :: MatchAnnot
  MatchAnnotCocaseOfCmd :: MatchAnnot
  deriving (Ord, Eq, Show)

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
  deriving (Ord, Eq, Show)

    