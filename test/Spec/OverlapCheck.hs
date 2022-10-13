module Spec.OverlapCheck where 

import Test.Hspec
import Syntax.CST.Terms
import Data.Text (Text, pack, unpack)
import Data.Maybe (isJust)
import Syntax.CST.Names (FreeVarName (MkFreeVarName), PrimName, XtorName (MkXtorName))
import Loc (Loc, defaultLoc)

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
test1 :: [Pattern]
test1 =
  [ PatXtor defaultLoc (MkXtorName (pack "Leaf")) [PatVar defaultLoc (MkFreeVarName (pack "x"))],
    PatXtor
      defaultLoc
      (MkXtorName (pack "Branch"))
      [ PatXtor defaultLoc (MkXtorName (pack "Leaf")) [PatVar defaultLoc (MkFreeVarName (pack "y"))],
        PatVar defaultLoc (MkFreeVarName (pack "t2"))
      ],
    PatVar defaultLoc (MkFreeVarName (pack "x")),
    PatStar defaultLoc,
    PatWildcard defaultLoc,
    PatXtor
      defaultLoc
      (MkXtorName (pack "Branch"))
      [ PatXtor defaultLoc (MkXtorName (pack "Leaf")) [PatVar defaultLoc (MkFreeVarName (pack "y"))],
        PatXtor defaultLoc (MkXtorName (pack "Leaf")) [PatVar defaultLoc (MkFreeVarName (pack "z"))]
      ],
    PatXtor
      defaultLoc
      (MkXtorName (pack "Branch"))
      [ PatVar defaultLoc (MkFreeVarName (pack "t1")),
        PatVar defaultLoc (MkFreeVarName (pack "t2"))
      ],
    PatVar defaultLoc (MkFreeVarName (pack "t"))
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
test2 :: [Pattern]
test2 =
  [ PatVar defaultLoc (MkFreeVarName (pack "m")),
    PatStar defaultLoc,
    PatXtor defaultLoc (MkXtorName (pack "Nothing")) [],
    PatXtor defaultLoc (MkXtorName (pack "Maybe")) [PatVar defaultLoc (MkFreeVarName (pack "x"))],
    PatWildcard defaultLoc
  ]

-- No Overlap expected.
test3 :: [Pattern]
test3 = []

-- No Overlap expected.
test4 :: [Pattern]
test4 = [PatStar defaultLoc]

-- (1) Node y Empty (Node z Empty Empty)
-- (2) Node z Empty Empty
-- No Overlap expected.
test5 :: [Pattern]
test5 =
  [ PatXtor
      defaultLoc
      (MkXtorName (pack "Node"))
      [ PatVar defaultLoc (MkFreeVarName (pack "y")),
        PatXtor defaultLoc (MkXtorName (pack "Empty")) [],
        PatXtor defaultLoc (MkXtorName (pack "Node")) [ PatVar defaultLoc (MkFreeVarName (pack "z")),
                                                        PatXtor defaultLoc (MkXtorName (pack "Empty")) [],
                                                        PatXtor defaultLoc (MkXtorName (pack "Empty")) []]],
    PatXtor
      defaultLoc
      (MkXtorName (pack "Node"))
      [ PatVar defaultLoc (MkFreeVarName (pack "z")),
        PatXtor defaultLoc (MkXtorName (pack "Empty")) [],
        PatXtor defaultLoc (MkXtorName (pack "Empty")) []]]

-- (1) x
-- (2) z
-- (3) x
-- -> Overlap expected between:
--    (1) and (2)
--    (1) and (3)
--    (2) and (3)
test6 :: [Pattern]
test6 =
  [ PatVar defaultLoc (MkFreeVarName (pack "x")),
    PatVar defaultLoc (MkFreeVarName (pack "z")),
    PatVar defaultLoc (MkFreeVarName (pack "x"))
  ]

-- (1) Cons x (Cons y (Cons z zs))
-- (2) Cons x (Cons y (Cons z (Cons m ms)))
-- -> Overlap expected between:
--    (1) and (2) (due to Subpattern Overlap between x and x, (Cons y (Cons z zs)) and (Cons y (Cons z (Cons m ms))))
test7 :: [Pattern]
test7 = [PatXtor defaultLoc (MkXtorName (pack "Cons")) 
          [ PatVar defaultLoc (MkFreeVarName (pack "x")),
            PatXtor defaultLoc (MkXtorName (pack "Cons")) 
              [ PatVar defaultLoc (MkFreeVarName (pack "y")),
                PatXtor defaultLoc (MkXtorName (pack "Cons")) [PatVar defaultLoc (MkFreeVarName (pack "z")), PatVar defaultLoc (MkFreeVarName (pack "zs"))]]],
         PatXtor defaultLoc (MkXtorName (pack "Cons")) 
          [PatVar defaultLoc (MkFreeVarName (pack "x")),
          PatXtor defaultLoc (MkXtorName (pack "Cons")) 
            [PatVar defaultLoc (MkFreeVarName (pack "y")),
            PatXtor defaultLoc (MkXtorName (pack "Cons")) 
              [PatVar defaultLoc (MkFreeVarName (pack "z")),
               PatXtor defaultLoc (MkXtorName (pack "Cons")) [PatVar defaultLoc (MkFreeVarName (pack "m")), PatVar defaultLoc (MkFreeVarName (pack "ms"))]]]]]

-- (1) Branch (Leaf x) (Leaf y)
-- (2) Branch (Leaf x) (Branch (Leaf y1) (Leaf y2))
-- No Overlap expected.
test8 :: [Pattern]
test8 = [PatXtor
          defaultLoc
          (MkXtorName (pack "Branch"))
          [ PatXtor defaultLoc (MkXtorName (pack "Leaf")) [PatVar defaultLoc (MkFreeVarName (pack "x"))],
            PatXtor defaultLoc (MkXtorName (pack "Leaf")) [PatVar defaultLoc (MkFreeVarName (pack "y"))]
          ],
         PatXtor
          defaultLoc
          (MkXtorName (pack "Branch"))
          [ PatXtor defaultLoc (MkXtorName (pack "Leaf")) [PatVar defaultLoc (MkFreeVarName (pack "x"))],
            PatXtor
            defaultLoc
            (MkXtorName (pack "Branch"))
            [ PatXtor defaultLoc (MkXtorName (pack "Leaf")) [PatVar defaultLoc (MkFreeVarName (pack "y1"))],
              PatXtor defaultLoc (MkXtorName (pack "Leaf")) [PatVar defaultLoc (MkFreeVarName (pack "y2"))]
            ]
          ]]

spec :: Spec
spec = describe "Foo" $ 
    it "bar" ((overlap test1) `shouldSatisfy` isJust)