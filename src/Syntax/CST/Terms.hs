module Syntax.CST.Terms where

import Data.Text (Text, pack)
import Data.List (tails)
import Loc (HasLoc (..), Loc)
import Syntax.CST.Names (FreeVarName, PrimName, XtorName, unFreeVarName, unXtorName)

--------------------------------------------------------------------------------------------
-- Substitutions
--------------------------------------------------------------------------------------------

data TermOrStar where
  ToSTerm :: Term -> TermOrStar
  ToSStar :: TermOrStar

deriving instance Show TermOrStar

deriving instance Eq TermOrStar

newtype Substitution = MkSubstitution {unSubstitution :: [Term]}

deriving instance Show Substitution

deriving instance Eq Substitution

newtype SubstitutionI = MkSubstitutionI {unSubstitutionI :: [TermOrStar]}

deriving instance Show SubstitutionI

deriving instance Eq SubstitutionI

--------------------------------------------------------------------------------------------
-- Patterns
--------------------------------------------------------------------------------------------

data Pattern where
  PatXtor :: Loc -> XtorName -> [Pattern] -> Pattern
  PatVar :: Loc -> FreeVarName -> Pattern
  PatStar :: Loc -> Pattern
  PatWildcard :: Loc -> Pattern

--------------------------------------------

type OverlapMsg = Text

type Overlap = Maybe OverlapMsg

-- | Generates the Overlap of Patterns between one another.
-- For testing purposes, best display via printOverlap $ overlap test<X>...
overlap :: [Pattern] -> Overlap
overlap l = let pairOverlaps = concat $ zipWith map (map (overlapA2) l) (tail (tails l))
            in  concatOverlaps pairOverlaps
  where
    -- | Reduces multiple potential Overlap Messages into one potential Overlap Message.
    concatOverlaps :: [Overlap] -> Overlap
    concatOverlaps xs =
      let concatRule = \x y -> x <> "\n\n" <> y
      in  foldr (liftm2 concatRule) Nothing xs
      where
        liftm2 :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
        liftm2 _ x          Nothing   = x
        liftm2 _ Nothing    y         = y
        liftm2 f (Just x)   (Just y)  = Just $ (f x y)

    -- | Generates an Overlap Message for patterns p1 p2.
    overlapMsg :: Pattern -> Pattern -> OverlapMsg
    overlapMsg p1 p2 =
      let p1Str = patternToText p1
          p2Str = patternToText p2
      in  "Overlap found:\n" <> p1Str <> " overlaps with " <> p2Str <> "\n"

    -- | Readable Conversion of Pattern to Text.
    patternToText :: Pattern -> Text
    patternToText (PatVar loc varName)     = pack("Variable Pattern ") <> (unFreeVarName varName) <> pack(" in: " ++ (show loc))
    patternToText (PatStar loc)            = pack $ "* Pattern in: " ++ (show loc)
    patternToText (PatWildcard loc)        = pack $ "Wildcard Pattern in: " ++ (show loc)
    patternToText (PatXtor loc xtorName _) = pack("Constructor Pattern ") <> (unXtorName xtorName) <> pack(" in: " ++ (show loc))

    -- | Determines for 2x Patterns p1 p2 a potential Overlap message on p1 'containing' p2 or p2 'containing' p1.
    overlapA2 :: Pattern -> Pattern -> Overlap
    -- An Overlap may occur for two De/Constructors if their Names match.
    overlapA2 p1@(PatXtor _ xXtorName xPatterns) 
              p2@(PatXtor _ yXtorName yPatterns) =
                if    xXtorName /= yXtorName
                then  Nothing
                else  let subPatternsOverlaps = zipWith overlapA2 xPatterns yPatterns
                          --Only if all Pairs of Subpatterns truly overlap is an Overlap found.
                          subPatternsOverlap =  if   (elem Nothing subPatternsOverlaps) 
                                                then Nothing 
                                                else concatOverlaps subPatternsOverlaps
                      in  case subPatternsOverlap of
                            Nothing                       -> Nothing
                            (Just subPatternsOverlapMsg)  ->
                              Just $
                                (overlapMsg p1 p2)
                                <> "due to the all Subpatterns overlapping as follows:\n"
                                <> "--------------------------------->\n"
                                <> subPatternsOverlapMsg
                                <> "---------------------------------<\n"
                                    
    -- If either p1 or p2 is no De/Constructor, they already overlap.
    overlapA2 p1 p2 = Just $ overlapMsg p1 p2

--------------------------------------------

deriving instance Show Pattern

deriving instance Eq Pattern

instance HasLoc Pattern where
  getLoc (PatXtor loc _ _) = loc
  getLoc (PatVar loc _) = loc
  getLoc (PatStar loc) = loc
  getLoc (PatWildcard loc) = loc

--------------------------------------------------------------------------------------------
-- Cases/Cocases
--------------------------------------------------------------------------------------------

data TermCase = MkTermCase
  { tmcase_loc :: Loc,
    tmcase_pat :: Pattern,
    tmcase_term :: Term
  }

deriving instance Show TermCase

deriving instance Eq TermCase

instance HasLoc TermCase where
  getLoc tc = tmcase_loc tc

--------------------------------------------------------------------------------------------
-- Terms
--------------------------------------------------------------------------------------------

data NominalStructural where
  Nominal :: NominalStructural
  Structural :: NominalStructural
  Refinement :: NominalStructural
  deriving (Eq, Ord, Show)

data Term where
  PrimTerm :: Loc -> PrimName -> Substitution -> Term
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
  PrimLitChar :: Loc -> Char -> Term
  PrimLitString :: Loc -> String -> Term
  NatLit :: Loc -> NominalStructural -> Int -> Term
  TermParens :: Loc -> Term -> Term
  FunApp :: Loc -> Term -> Term -> Term
  Lambda :: Loc -> FreeVarName -> Term -> Term
  CoLambda :: Loc -> FreeVarName -> Term -> Term
  Apply :: Loc -> Term -> Term -> Term

deriving instance Show Term

deriving instance Eq Term

instance HasLoc Term where
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
  getLoc (PrimLitChar loc _) = loc
  getLoc (PrimLitString loc _) = loc
  getLoc (NatLit loc _ _) = loc
  getLoc (TermParens loc _) = loc
  getLoc (FunApp loc _ _) = loc
  getLoc (Lambda loc _ _) = loc
  getLoc (CoLambda loc _ _) = loc
  getLoc (Apply loc _ _) = loc
  getLoc (PrimTerm loc _ _) = loc
