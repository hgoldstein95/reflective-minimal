{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module Bound5Example where

import Control.Lens (Profunctor (lmap), makePrisms, _1, _2, _3, _4, _5)
import Data.Bits (shiftL)
import Data.Int (Int16)
import Freer (FR)
import qualified Freer as FR
import GHC.Generics (Generic)
import Test.QuickCheck (Arbitrary (..), genericShrink)

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
  arbitrary = FR.gen reflT
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