{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Bound5Example where

import Control.Lens (Profunctor (lmap), makePrisms, _1, _2, _3, _4, _5)
import Control.Monad (replicateM)
import Data.Bits (shiftL)
import Data.Int (Int16)
import Freer (FR)
import qualified Freer as FR
import GHC.Generics (Generic)
import Test.QuickCheck
  ( Arbitrary (..),
    Args (chatty, maxShrinks, maxSize, maxSuccess),
    Result (Failure, failingTestCase),
    Testable (propertyForAllShrinkShow),
    genericShrink,
    quickCheckWithResult,
    shrinkNothing,
    stdArgs,
  )

type I = [Int16]

data T = T I I I I I
  deriving (Generic, Eq, Ord, Show, Read)

makePrisms ''T

toList :: T -> [[Int16]]
toList (T i0 i1 i2 i3 i4) = [i0, i1, i2, i3, i4]

pre :: T -> Bool
pre t = all ((< 256) . sum) (toList t)

post :: T -> Bool
post t = (sum . concat) (toList t) < 5 * 256

prop :: T -> Bool
prop t = not (pre t) || post t

size :: T -> Int
size = length . concat . toList

instance Arbitrary T where
  arbitrary = T <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary
  shrink = genericShrink

int16 :: FR Int16 Int16
int16 =
  let mn = (minBound :: Int16)
      mx = (maxBound :: Int16)
      ilog2 1 = 0
      ilog2 n | n > 0 = 1 + ilog2 (n `div` 2)
      ilog2 _ = error "ilog2"

      -- How many bits are needed to represent this type?
      -- (This number is an upper bound, not exact.)
      bits = ilog2 (toInteger mx - toInteger mn + 1)
   in FR.sized $ \k ->
        let -- Reach maximum size by k=80, or quicker for small integer types
            power = ((bits `max` 40) * k) `div` 80

            -- Bounds should be 2^power, but:
            --   * clamp the result to minBound/maxBound
            --   * clamp power to 'bits', in case k is a huge number
            lo = toInteger mn `max` (-1 `shiftL` (power `min` bits))
            hi = toInteger mx `min` (1 `shiftL` (power `min` bits))
         in lmap fromIntegral $ fromInteger <$> FR.chooseInteger (lo, hi)

reflT :: FR T T
reflT =
  T
    <$> FR.focus (_T . _1) (FR.listOf int16)
    <*> FR.focus (_T . _2) (FR.listOf int16)
    <*> FR.focus (_T . _3) (FR.listOf int16)
    <*> FR.focus (_T . _4) (FR.listOf int16)
    <*> FR.focus (_T . _5) (FR.listOf int16)

counterExampleNone :: (Show a, Read a, Arbitrary a) => (a -> Bool) -> IO a
counterExampleNone p =
  quickCheckWithResult (stdArgs {chatty = False, maxSuccess = 10000}) (propertyForAllShrinkShow arbitrary shrinkNothing ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleNone: no counterexample found"

counterExampleGeneric :: (Show a, Read a, Arbitrary a) => (a -> Bool) -> (a -> Bool) -> IO a
counterExampleGeneric p inv =
  quickCheckWithResult (stdArgs {chatty = False, maxSuccess = 10000}) (propertyForAllShrinkShow arbitrary (filter inv . shrink) ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleGeneric: no counterexample found"

counterExampleFR :: (Eq a, Show a, Read a) => FR a a -> (a -> Bool) -> IO a
counterExampleFR g p =
  quickCheckWithResult (stdArgs {chatty = False, maxSuccess = 10000, maxSize = 30, maxShrinks = 1}) (propertyForAllShrinkShow (FR.gen g) (\v -> let v' = FR.shrink (not . p) g v in [v' | v /= v']) ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleFR: no counterexample found"

average :: [Int] -> Double
average xs = fromIntegral (sum xs) / fromIntegral (length xs)

main :: Int -> IO (Double, Double, Double)
main n = do
  putStr "bound5: "
  x <- measure $ counterExampleNone prop
  y <- measure $ counterExampleGeneric prop pre
  z <- measure $ counterExampleFR reflT prop
  pure (x, y, z)
  where
    measure x = do
      xs <- replicateM n x
      pure $ average (size <$> xs)