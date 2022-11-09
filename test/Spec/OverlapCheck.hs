module Spec.OverlapCheck where 

import Test.Hspec
import Syntax.RST.Terms
import Syntax.CST.Terms(NominalStructural(Nominal))
import Syntax.CST.Types
import Data.Text (pack, unpack)
import Data.Maybe (isJust, isNothing)
import Syntax.CST.Names (FreeVarName (MkFreeVarName), XtorName (MkXtorName))
import Loc (defaultLoc)

-----------------------------------------------------------
-- Producer only tests:
-----------------------------------------------------------

-- (1) Leaf x 
-- (2) Branch (Leaf y) t2 
-- (3) x
-- (4) *
-- (5) _
-- (6) Branch (Leaf y) (Leaf z)
-- (7) Branch t1 t2 
-- (8) t
-- -> Overlap expected between:
--    (1) and (3)
--    (1) and (4)
--    (1) and (5)
--    (1) and (8)
--    (2) and (3)
--    (2) and (4)
--    (2) and (5)
--    (2) and (6) due to Subpattern matches of (Leaf y) and (Leaf y), t2 and (Leaf z)
--    (2) and (7) due to Subpattern matches of (Leaf y) and t1, t2 and t2
--    (2) and (8)
--    (3) and (4)
--    (3) and (5)
--    (3) and (6)
--    (3) and (7)
--    (3) and (8)
--    (4) and (5)
--    (4) and (6)
--    (4) and (7)
--    (4) and (8)
--    (6) and (7) due to Subpattern matches of (Leaf y) and t1, (Leaf z) and t2
--    (6) and (8)
--    (7) and (8)
test1 :: [PatternNew]
test1 =
  [ PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "x"))],
    PatXtor
      defaultLoc Prd Nominal 
      (MkXtorName (pack "Branch"))
      [ PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "y"))],
        PatVar defaultLoc Prd (MkFreeVarName (pack "t2"))
      ],
    PatVar defaultLoc Prd (MkFreeVarName (pack "x")),
    --PatStar defaultLoc Prd,
    PatWildcard defaultLoc Prd,
    PatXtor
      defaultLoc Prd Nominal 
      (MkXtorName (pack "Branch"))
      [ PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "y"))],
        PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "z"))]
      ],
    PatXtor
      defaultLoc Prd Nominal 
      (MkXtorName (pack "Branch"))
      [ PatVar defaultLoc Prd (MkFreeVarName (pack "t1")),
        PatVar defaultLoc Prd (MkFreeVarName (pack "t2"))
      ],
    PatVar defaultLoc Prd (MkFreeVarName (pack "t"))
  ]

-- (1) m
-- (2) *
-- (3) Nothing 
-- (4) Maybe x 
-- (5) _
-- -> Overlap expected between:
--    (1) and (2)
--    (1) and (3)
--    (1) and (4)
--    (1) and (5)
--    (2) and (3)
--    (2) and (4)
--    (2) and (5)
--    (3) and (5)
--    (4) and (5)
test2 :: [PatternNew]
test2 =
  [ PatVar defaultLoc Prd (MkFreeVarName (pack "m")),
    --PatStar defaultLoc Prd,
    PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Nothing")) [],
    PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Maybe")) [PatVar defaultLoc Prd (MkFreeVarName (pack "x"))],
    PatWildcard defaultLoc Prd
  ]

-- No Overlap expected.
test3 :: [PatternNew]
test3 = []

-- No Overlap expected.
test4 :: [PatternNew]
test4 = [
  --PatStar defaultLoc Prd
  ]

-- (1) Node y Empty (Node z Empty Empty)
-- (2) Node z Empty Empty
-- No Overlap expected.
test5 :: [PatternNew]
test5 =
  [ PatXtor
      defaultLoc Prd Nominal 
      (MkXtorName (pack "Node"))
      [ PatVar defaultLoc Prd (MkFreeVarName (pack "y")),
        PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Empty")) [],
        PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Node")) [ PatVar defaultLoc Prd (MkFreeVarName (pack "z")),
                                                        PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Empty")) [],
                                                        PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Empty")) []]],
    PatXtor
      defaultLoc Prd Nominal 
      (MkXtorName (pack "Node"))
      [ PatVar defaultLoc Prd (MkFreeVarName (pack "z")),
        PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Empty")) [],
        PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Empty")) []]]

-- (1) x
-- (2) z
-- (3) x
-- -> Overlap expected between:
--    (1) and (2)
--    (1) and (3)
--    (2) and (3)
test6 :: [PatternNew]
test6 =
  [ PatVar defaultLoc Prd (MkFreeVarName (pack "x")),
    PatVar defaultLoc Prd (MkFreeVarName (pack "z")),
    PatVar defaultLoc Prd (MkFreeVarName (pack "x"))
  ]

-- (1) Cons x (Cons y (Cons z zs))
-- (2) Cons x (Cons y (Cons z (Cons m ms)))
-- -> Overlap expected between:
--    (1) and (2) (due to Subpattern Overlap between x and x, (Cons y (Cons z zs)) and (Cons y (Cons z (Cons m ms))))
test7 :: [PatternNew]
test7 = [PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Cons")) 
          [ PatVar defaultLoc Prd (MkFreeVarName (pack "x")),
            PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Cons")) 
              [ PatVar defaultLoc Prd (MkFreeVarName (pack "y")),
                PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Cons")) [PatVar defaultLoc Prd (MkFreeVarName (pack "z")), PatVar defaultLoc Prd (MkFreeVarName (pack "zs"))]]],
         PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Cons")) 
          [PatVar defaultLoc Prd (MkFreeVarName (pack "x")),
          PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Cons")) 
            [PatVar defaultLoc Prd (MkFreeVarName (pack "y")),
            PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Cons")) 
              [PatVar defaultLoc Prd (MkFreeVarName (pack "z")),
               PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Cons")) [PatVar defaultLoc Prd (MkFreeVarName (pack "m")), PatVar defaultLoc Prd (MkFreeVarName (pack "ms"))]]]]]

-- (1) Branch (Leaf x) (Leaf y)
-- (2) Branch (Leaf x) (Branch (Leaf y1) (Leaf y2))
-- No Overlap expected.
test8 :: [PatternNew]
test8 = [PatXtor
          defaultLoc Prd Nominal 
          (MkXtorName (pack "Branch"))
          [ PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "x"))],
            PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "y"))]
          ],
         PatXtor
          defaultLoc Prd Nominal 
          (MkXtorName (pack "Branch"))
          [ PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "x"))],
            PatXtor 
            defaultLoc Prd Nominal 
            (MkXtorName (pack "Branch"))
            [ PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "y1"))],
              PatXtor defaultLoc Prd Nominal (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "y2"))]
            ]
          ]]

-----------------------------------------------------------
-- Mixed Producer & Consumer tests (taken from examples\NestedPatternMatch.duo):
-----------------------------------------------------------




-----------------------------------------------------------
-- Executing tests:
-----------------------------------------------------------

-- | Helper for readable display of Overlap objects, testing with printOverlap $ overlap test<X>
printOverlap :: Overlap -> IO ()
printOverlap (Just msg) = putStrLn $ unpack msg 
printOverlap Nothing    = putStrLn $ "No Overlap found."

spec :: Spec
spec = do 
  describe "Checking test1 in OverlapCheck.hs for Overlap." $ it "Found Overlap." ((overlap test1) `shouldSatisfy` isJust)
  describe "Checking test2 in OverlapCheck.hs for Overlap." $ it "Found Overlap." ((overlap test2) `shouldSatisfy` isJust)
  describe "Checking test3 in OverlapCheck.hs for Overlap." $ it "Found no Overlap." ((overlap test3) `shouldSatisfy` isNothing)
  describe "Checking test4 in OverlapCheck.hs for Overlap." $ it "Found no Overlap." ((overlap test4) `shouldSatisfy` isNothing)
  describe "Checking test5 in OverlapCheck.hs for Overlap." $ it "Found no Overlap." ((overlap test5) `shouldSatisfy` isNothing)
  describe "Checking test6 in OverlapCheck.hs for Overlap." $ it "Found Overlap." ((overlap test6) `shouldSatisfy` isJust)
  describe "Checking test7 in OverlapCheck.hs for Overlap." $ it "Found Overlap." ((overlap test7) `shouldSatisfy` isJust)
  describe "Checking test8 in OverlapCheck.hs for Overlap." $ it "Found no Overlap." ((overlap test8) `shouldSatisfy` isNothing)