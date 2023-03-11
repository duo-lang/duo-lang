module Spec.OverlapCheck where 

import Test.Hspec
import Syntax.RST.Terms 
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
-- (7) Branch t1 * 
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
--    (2) and (7) due to Subpattern matches of (Leaf y) and t1, t2 and *
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
--    (6) and (7) due to Subpattern matches of (Leaf y) and t1, (Leaf z) and *
--    (6) and (8)
--    (7) and (8)
test1 :: [GenericPattern]
test1 =
  [ Left $ PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "x"))],
    Left $ PatXtor
      defaultLoc Prd (Nominal Nothing) 
      (MkXtorName (pack "Branch"))
      [ PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "y"))],
        PatVar defaultLoc Prd (MkFreeVarName (pack "t2"))
      ],
    Left $ PatVar defaultLoc Prd (MkFreeVarName (pack "x")),
    Right $ PatStar defaultLoc Prd,
    Left $ PatWildcard defaultLoc Prd,
    Left $ PatXtor
      defaultLoc Prd (Nominal Nothing) 
      (MkXtorName (pack "Branch"))
      [ PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "y"))],
        PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "z"))]
      ],
    Right $ PatXtorStar
      defaultLoc Prd (Nominal Nothing) 
      (MkXtorName (pack "Branch"))
      ([ PatVar defaultLoc Prd (MkFreeVarName (pack "t1"))], PatStar defaultLoc Prd, []),
    Left $ PatVar defaultLoc Prd (MkFreeVarName (pack "t"))
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
test2 :: [GenericPattern]
test2 =
  [ Left $ PatVar defaultLoc Prd (MkFreeVarName (pack "m")),
    Right $ PatStar defaultLoc Prd,
    Left $ PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Nothing")) [],
    Left $ PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Maybe")) [PatVar defaultLoc Prd (MkFreeVarName (pack "x"))],
    Left $ PatWildcard defaultLoc Prd
  ]

-- No Overlap expected.
test3 :: [GenericPattern]
test3 = []

-- No Overlap expected.
test4 :: [GenericPattern]
test4 = [
  Right $ PatStar defaultLoc Prd
  ]

-- (1) Node y Empty (Node z Empty Empty)
-- (2) Node z Empty Empty
-- No Overlap expected.
test5 :: [GenericPattern]
test5 =
  [ Left $ PatXtor
      defaultLoc Prd (Nominal Nothing) 
      (MkXtorName (pack "Node"))
      [ PatVar defaultLoc Prd (MkFreeVarName (pack "y")),
        PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Empty")) [],
        PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Node")) [ PatVar defaultLoc Prd (MkFreeVarName (pack "z")),
                                                        PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Empty")) [],
                                                        PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Empty")) []]],
    Left $ PatXtor
      defaultLoc Prd (Nominal Nothing) 
      (MkXtorName (pack "Node"))
      [ PatVar defaultLoc Prd (MkFreeVarName (pack "z")),
        PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Empty")) [],
        PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Empty")) []]]

-- (1) x
-- (2) z
-- (3) x
-- -> Overlap expected between:
--    (1) and (2)
--    (1) and (3)
--    (2) and (3)
test6 :: [GenericPattern]
test6 =
  [ Left $ PatVar defaultLoc Prd (MkFreeVarName (pack "x")),
    Left $ PatVar defaultLoc Prd (MkFreeVarName (pack "z")),
    Left $ PatVar defaultLoc Prd (MkFreeVarName (pack "x"))
  ]

-- (1) Cons x (Cons y (Cons z zs))
-- (2) Cons x (Cons y (Cons z (Cons m ms)))
-- -> Overlap expected between:
--    (1) and (2) (due to Subpattern Overlap between x and x, (Cons y (Cons z zs)) and (Cons y (Cons z (Cons m ms))))
test7 :: [GenericPattern]
test7 = [Left $ PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Cons")) 
          [ PatVar defaultLoc Prd (MkFreeVarName (pack "x")),
            PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Cons")) 
              [ PatVar defaultLoc Prd (MkFreeVarName (pack "y")),
                PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Cons")) [PatVar defaultLoc Prd (MkFreeVarName (pack "z")), PatVar defaultLoc Prd (MkFreeVarName (pack "zs"))]]],
         Left $ PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Cons")) 
          [PatVar defaultLoc Prd (MkFreeVarName (pack "x")),
          PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Cons")) 
            [PatVar defaultLoc Prd (MkFreeVarName (pack "y")),
            PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Cons")) 
              [PatVar defaultLoc Prd (MkFreeVarName (pack "z")),
               PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Cons")) [PatVar defaultLoc Prd (MkFreeVarName (pack "m")), PatVar defaultLoc Prd (MkFreeVarName (pack "ms"))]]]]]

-- (1) Branch (Leaf x) (Leaf y)
-- (2) Branch (Leaf x) (Branch (Leaf y1) (Leaf y2))
-- No Overlap expected.
test8 :: [GenericPattern]
test8 = [Left $ PatXtor
          defaultLoc Prd (Nominal Nothing) 
          (MkXtorName (pack "Branch"))
          [ PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "x"))],
            PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "y"))]
          ],
         Left $ PatXtor
          defaultLoc Prd (Nominal Nothing) 
          (MkXtorName (pack "Branch"))
          [ PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "x"))],
            PatXtor 
            defaultLoc Prd (Nominal Nothing) 
            (MkXtorName (pack "Branch"))
            [ PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "y1"))],
              PatXtor defaultLoc Prd (Nominal Nothing) (MkXtorName (pack "Leaf")) [PatVar defaultLoc Prd (MkFreeVarName (pack "y2"))]
            ]
          ]]

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