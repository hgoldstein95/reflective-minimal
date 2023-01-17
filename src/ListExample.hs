{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ListExample where

--------------------------------------------------------------------------
-- imports

import Control.Monad (replicateM)
import Freer (FR)
import qualified Freer as FR
import Test.QuickCheck
  ( Arbitrary (..),
    Args (chatty),
    Result (Failure, failingTestCase),
    Testable (propertyForAllShrinkShow),
    quickCheckWithResult,
    shrinkNothing,
    stdArgs,
  )

prop_Reverse :: [Int] -> Bool
prop_Reverse xs = reverse xs == xs

counterExampleNone :: (Show a, Read a, Arbitrary a) => (a -> Bool) -> IO a
counterExampleNone p =
  quickCheckWithResult (stdArgs {chatty = False}) (propertyForAllShrinkShow arbitrary shrinkNothing ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleFR: no counterexample found"

counterExampleGeneric :: (Show a, Read a, Arbitrary a) => (a -> Bool) -> (a -> Bool) -> IO a
counterExampleGeneric p inv =
  quickCheckWithResult (stdArgs {chatty = False}) (propertyForAllShrinkShow arbitrary (filter inv . shrink) ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleFR: no counterexample found"

counterExampleFR :: (Eq a, Show a, Read a) => FR a a -> (a -> Bool) -> IO a
counterExampleFR g p =
  quickCheckWithResult (stdArgs {chatty = False}) (propertyForAllShrinkShow (FR.gen g) (\v -> let v' = FR.shrink (not . p) g v in [v' | v /= v']) ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleFR: no counterexample found"

average :: [Int] -> Double
average xs = fromIntegral (sum xs) / fromIntegral (length xs)

main :: IO ()
main = do
  measure $ counterExampleNone prop_Reverse
  measure $ counterExampleGeneric prop_Reverse (const True)
  measure $ counterExampleFR (FR.listOf FR.integer) prop_Reverse
  where
    measure x = do
      xs <- replicateM 100 x
      print $ average (length <$> xs)