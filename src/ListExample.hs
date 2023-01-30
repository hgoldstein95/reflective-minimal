{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ListExample where

import Data.Profunctor (lmap)
import Freer (FR, gen, integer, listOf)
import GHC.Generics (Generic)
import Test.QuickCheck (Arbitrary (..), genericShrink)

--------------------------------------------------------------------------
-- imports

newtype IntList = IntList [Int]
  deriving (Generic, Eq, Read, Show)

size :: IntList -> Int
size (IntList xs) = length xs

reflList :: FR IntList IntList
reflList = IntList <$> lmap (\case IntList xs -> xs) (listOf integer)

invariant :: b -> Bool
invariant = const True

prop_Reverse :: IntList -> Bool
prop_Reverse (IntList xs) = reverse xs == xs

instance Arbitrary IntList where
  arbitrary = gen reflList
  shrink = genericShrink
