{-

Exhibits the fan out property of Reflective Generators.

-}
module FanOut where

import Control.Lens ( _head, _tail)
import Data.List (group, maximumBy, sort)
import Interps
import Reflectives


-- Reflective generator that deliberately has a fan out of one
fanOut1 :: Reflective Int Int
fanOut1 = exact 1 -- It just generates one, one way

-- Reflective generator that deliberately has a fan out of two
fanOut2 :: Reflective Int Int
fanOut2 = oneof [exact 1, exact 1] -- It just generates one, two ways

-- Reflective generator that deliberately has a max fan out of one
fanOut1' :: Reflective Int Int
fanOut1' = oneof [exact 1, exact 2] -- It just generates one, one way, and two one way

-- Reflective generator that deliberately has a max fan out of two
fanOut2' :: Reflective Int Int
fanOut2' = oneof [exact 1, exact 1, exact 2] -- It just generates one, two ways, and two one way

-- Find the max fan out of a reflective
-- becomes slow for bst (1,7), taking about three second, says fan out of 1
findMaxFO :: (Ord b) => Reflective a b -> Int
findMaxFO = maximum . fmap length . group . sort . enum

-- Find the max fan out of a reflective and which value has that
findMaxFO' :: (Ord b) => Reflective a b -> (Int, b)
findMaxFO' = maximumBy (\(x,_) (y,_) -> compare x y) . fmap (\xs -> (length xs, head xs))
           . group . sort . enum

-- the above are obviously too slow to be tractable on any read reflectives, but
-- the purpose of this property is to clearly explain what fanout is, not implement
-- it efficiently

infFanOut :: Reflective [Int] [Int]
infFanOut =
  oneof
    [ infFanOut,
      exact [],
      do
        x <- focus _head (choose (0, 10))
        xs <- focus _tail infFanOut
        exact (x : xs)
    ]