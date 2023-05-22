{-# LANGUAGE GADTs, GeneralizedNewtypeDeriving, FlexibleContexts #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module DependentTests where

import Control.Monad.Except (forM)
import Control.Monad ( foldM, join )

import Test.Hspec ( hspec, describe, Spec, pending, it )

import Data.Maybe (fromJust, isJust, catMaybes, isNothing, fromMaybe)
import Data.List (transpose, delete)
import Control.Monad.Reader
import Control.Monad.State
import Unsafe.Coerce ( unsafeCoerce )

type Description = String

-----------------------------------------------------------------------------------
---------Building it as a Monad-----------

-- The config can be set when building a new TestM, 

-- DefConf      skips all tests, for which vertical dependencies are not fullfilled
-- PendingConf  shows those tests as pending 
data Config = DefConf | PendingConf

-- The test results are stored via type hiding, as not all testresults will have the same type
data TestResult = forall a. TestResult a
-- All results will also be stored with an index, which can be used to define horizontal dependencies
type TestResults = [[Maybe TestResult]]

-- The Teststate:
data TestState = TestState {tests :: TestResults           -- testresults of previous tests
                            , testSpecs :: Spec              -- the spectests, ready to be run
                            }

initialTestState :: TestState
initialTestState = TestState {tests = [], testSpecs = return ()}

-- TestState Monad: 
-- A Monadstack now bringing the TestState and Config together
newtype TestM m a = MkTestM {runTestM :: ReaderT Config (StateT TestState m) a}
  deriving (Applicative, Functor, Monad, MonadIO, MonadState TestState, MonadReader Config)


liftTestM :: (Monad m) => m a -> TestM m a
liftTestM = MkTestM . lift . lift

------------------------------------------
-- Helper functions for testing: 

-- Add a testresult (tuple of results and spec) to the state
addTestResult :: MonadState TestState m => ([Maybe b], Spec) -> m ()
addTestResult (result, spec) = modify (\s -> s {tests = (fmap TestResult <$> result) : tests s,
                                                testSpecs = testSpecs s >> spec})

getTestId :: MonadState TestState m => m Int
getTestId = do 
  t <- gets tests
  return $ length t

getExamplesById :: MonadState TestState m => Int -> m [Maybe TestResult]
getExamplesById id = do
  t <- gets tests
  return $ (t!!id)



-- For horizontal dependencies: bringing together the current examples to be tested (exs)
-- and filter them, so that only those for which the deps are not Nothing are kept as `Just` values
zipExamplesWithDeps :: [Maybe a] -> [[Maybe TestResult]] -> [Maybe a]
zipExamplesWithDeps exs deps = case exs of
  [] -> []
  (Nothing : xs) -> Nothing : zipExamplesWithDeps xs (map tail deps)
  (Just x : xs) -> let depsAtIndex = map head deps
                   in (if all isJust depsAtIndex then Just x else Nothing)
                      : zipExamplesWithDeps xs (map tail deps)

-- filter examples with a list of ids, which are the ids for horizontal dependencies
extractDeps :: MonadState TestState m => [Int] -> [Maybe a] -> m [Maybe a]
extractDeps ids exs = do
  stateTests <- gets tests
  let deps = map (\id -> stateTests!!id) ids
      result = zipExamplesWithDeps exs deps
  return result


---------------------------------------------------------
---- pre configured settings 
noDeps :: (a -> Maybe [a], [Int])
noDeps = (const Nothing, [])
------------------------------------------
-- The core of this library - runTest

-- Arguments: 
-- descr          A description for the test
-- exs            A list of examples to be tested. Nothing values will be skipped
-- dependencies   A tuple with a dependency function (calculating a list of vertical dependencies)
--                       , and a List of indices, serving as horizontal dependencies
-- spectest       The spectest that is to be run over every example, returning a result and a spec

-- Returns: An tuple (Int, [Maybe b]), which depict an index for these testresults (to give to other tests as horizontal dep.) and
--                                                  a List of the results (if a test was not successfull, its index will be filled 
--                                                                         with a `Nothing`)
runTest :: (Eq a) => Monad m =>
                    Description
                  -> [Maybe a]                     
                  -> (a -> Maybe [a], [Int])       
                  -> (a -> m (Maybe b, Spec))
                  -> TestM m Int                   
runTest descr exs (depFunc, depIds) spectest = do
  conf <- ask
  -- filter horizontal dependencies
  horizontalDepTests <- extractDeps depIds exs

  -- actually run tests
  tested <- dependencyTesting [] horizontalDepTests depFunc spectest

  let results = case conf of
                  DefConf -> map (join . fmap (`lookup` tested)) exs
                  PendingConf -> map (fmap (\val -> fromMaybe
                    (Nothing, it "The dependencies were not fullfilled" $ do pending)
                    (lookup val tested)))
                                 exs
  -- extract results of test runs
  let bs = map (join . fmap fst) results
  -- extract and combine test display output
  let specs = mapM_ snd (catMaybes results)
  testId <- getTestId
  addTestResult (bs, describe descr specs)
  return testId

---------------------------------------------------------
--------- Dependent tests (giving one id instead of a list of values for testing)------------


runTestFromResult :: (Eq a) => Monad m =>
                    Description
                  -> Int                                    -- Values to be tested
                  -> (a -> Maybe [a], [Int])                -- Function for dependencies
                  -> (a -> m (Maybe b, Spec))
                  -> TestM m Int                            -- returns just the id of the test
runTestFromResult descr exId (depFunc, depIds) spectest = do
  conf <- ask
  -- get the testresults associated with the given index
  exs <- getExamplesById exId
  -- filter with dependencies
  horizontalDepTests <- extractDeps depIds exs


  -- Run tests with vertical dependencies (they are not in the cache so far)
  -- TODO: Maybe run 
  tested <- dependencyTestingTR [] horizontalDepTests depFunc spectest

  let results = case conf of
                  DefConf -> map (\tr -> case tr of 
                                    Nothing -> Nothing
                                    Just (TestResult tr) -> (lookup (unsafeCoerce tr) tested)) exs
                  PendingConf -> map (fmap (\(TestResult tr) -> fromMaybe
                    (Nothing, it "The dependencies were not fullfilled" $ do pending)
                    (lookup (unsafeCoerce tr) tested)))
                                 exs
  -- extract results of test runs
  let bs = map (join . fmap fst) results
  -- extract and combine test display output
  let specs = mapM_ snd (catMaybes results)
  testId <- getTestId
  addTestResult (bs, describe descr specs)
  return testId


dependencyTesting :: Eq a => Monad m =>
                             [(a, (Maybe b, Spec))]                -- Collection of result list
                             -> [Maybe a]                          -- Values to be tested
                             -> (a -> Maybe [a])                   -- DependencyFunction  
                             -> (a -> m (Maybe b, Spec))           -- spectest
                             -> TestM m [(a, (Maybe b, Spec))]
dependencyTesting steps [] _ _ = return steps
dependencyTesting steps (Nothing: as) depFunc spectest = dependencyTesting steps as depFunc spectest
dependencyTesting resMap (Just x : as) depFunc spectest =
  case lookup x resMap of
    Just _  -> dependencyTesting resMap as depFunc spectest
    Nothing ->
      let dependencies = depFunc x
      in case dependencies of
        Nothing -> do                                  
           testResult <- liftTestM $ spectest x
           dependencyTesting ((x, testResult):resMap) as depFunc spectest
        Just deps -> do
          resMap' <- dependencyTesting resMap (map Just deps) depFunc spectest
          let dependenciesFullfilled = all (\dep -> case lookup dep resMap' of
                                                     Just (Just _, _) -> True
                                                     _                -> False)
                                            deps
          if dependenciesFullfilled then do
                                      testResult <- liftTestM $ spectest x
                                      dependencyTesting ((x, testResult):resMap) as depFunc spectest
                                    else dependencyTesting resMap' as depFunc spectest


-- DependencyTestingTR is supposed to do the same thing as dependencyTesting, 
-- but utilizing TestResult
dependencyTestingTR :: Eq a => Monad m =>
                             [(a, (Maybe b, Spec))]                -- Collection of result list
                             -> [Maybe TestResult]                 -- Values to be tested
                             -> (a -> Maybe [a])                   -- DependencyFunction  
                             -> (a -> m (Maybe b, Spec))           -- spectest
                             -> TestM m [(a, (Maybe b, Spec))]
dependencyTestingTR steps [] _ _ = return steps
dependencyTestingTR steps (Nothing: as) depFunc spectest = dependencyTestingTR steps as depFunc spectest
dependencyTestingTR resMap (Just (TestResult x) : as) depFunc spectest =
  case lookup (unsafeCoerce x) resMap of
    Just _  -> dependencyTestingTR resMap as depFunc spectest
    Nothing ->
      let dependencies = depFunc $ unsafeCoerce x
      in case dependencies of
        Nothing -> do                                  
           specTestResult <- liftTestM $ spectest $ unsafeCoerce x
           dependencyTestingTR ((unsafeCoerce x, specTestResult):resMap) as depFunc spectest
        Just deps -> do
          resMap' <- dependencyTestingTR resMap (map (Just . TestResult) deps) depFunc spectest
          let dependenciesFullfilled = all (\dep -> case lookup dep resMap' of
                                                     Just (Just _, _) -> True
                                                     _                -> False)
                                            deps
          if dependenciesFullfilled then do
                                      testResult <- liftTestM $ spectest $ unsafeCoerce x
                                      dependencyTestingTR ((unsafeCoerce x, testResult):resMap') as depFunc spectest
                                    else dependencyTestingTR resMap' as depFunc spectest