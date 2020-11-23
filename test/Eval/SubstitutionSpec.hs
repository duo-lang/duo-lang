{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleInstances #-}
module Eval.SubstitutionSpec where

import Test.Hspec
import Control.Monad (forM_, when)
import Test.QuickCheck
import qualified Data.Map as M

import Syntax.Terms
import Eval.Substitution
import Utils

instance Arbitrary a => Arbitrary (Twice [a]) where
  arbitrary = sized $ \n -> do
    i1 <- choose (0,4)
    i2 <- choose (0,4)
    args1 <- resize (n `div` (i1 + 1)) $ vector i1
    args2 <- resize (n `div` (i2 + 1)) $ vector i2
    return (Twice args1 args2)

instance Arbitrary PrdOrCns where
  arbitrary = oneof [return Prd, return Cns]

instance Arbitrary DataOrCodata where
  arbitrary = oneof [return Data, return Codata]

arbitraryTermOpen :: Arbitrary a => PrdOrCns -> Gen (Term a)
arbitraryTermOpen x = sized foo
  where
    foo n | n <= 1    = oneof [ FreeVar <$> arbitrary <*> arbitrary]
          | otherwise = oneof [ FreeVar <$> arbitrary <*> arbitrary
                              , XtorCall <$> arbitrary <*> arbitrary <*> arbitrary
                              ]

instance Arbitrary a => Arbitrary (Term a) where
  arbitrary = oneof [arbitraryTermOpen Prd, arbitraryTermOpen Cns]


instance Arbitrary a => Arbitrary (Command a) where
  arbitrary = sized foo
    where
      foo n | n <= 1 = return Done
            | otherwise = oneof [ return Done
                                , Print <$> arbitrary
                                , Apply <$> resize (n `div` 2) arbitrary <*> resize (n `div` 2) arbitrary
                                ]


termOpeningClosingSingle :: Term () -> Bool
termOpeningClosingSingle t | null (freeVars_term t) = True
                           | otherwise = let v = head (freeVars_term t)
                                         in termOpeningSingle Prd (FreeVar v ()) (termClosingSingle Prd v t) == t

commandOpeningClosingSingle :: Command () -> Bool
commandOpeningClosingSingle c | null (freeVars_cmd c) = True
                              | otherwise = let v = head (freeVars_cmd c)
                                in commandOpeningSingle Prd (FreeVar v ()) (commandClosingSingle Prd v c) == c

spec :: Spec
spec = do
  -- Debugging the generator:
  _ <- runIO (sample (arbitrary @(Term ())))
  describe "\"Locally Nameless\" operations are correctly implemented" $ do
    it "termOpeningSingle . termClosingSingle = id" $ do
      property termOpeningClosingSingle
    it "commandOpeningSingle . commandClosingSingle = id" $ do
      property commandOpeningClosingSingle
