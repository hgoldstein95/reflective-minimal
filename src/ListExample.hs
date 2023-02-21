{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}

module ListExample where

import Freer (Reflective, generate, integer, listOf, lmap)
import GHC.Generics (Generic)
import Test.QuickCheck (Arbitrary (..), genericShrink)

-- From SmartCheck

newtype IntList = IntList [Int]
  deriving (Generic, Eq, Read, Show)

size :: IntList -> Int
size (IntList xs) = length xs

reflList :: Reflective IntList IntList
reflList = IntList <$> lmap (\case IntList xs -> xs) (listOf integer)

invariant :: b -> Bool
invariant = const True

instance Arbitrary IntList where
  arbitrary = generate reflList -- Modified
  shrink = genericShrink

-- Reflective Generator

prop_Reverse :: IntList -> Bool
prop_Reverse (IntList xs) = reverse xs == xs