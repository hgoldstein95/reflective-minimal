{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module HeapExample where

import Control.Lens (makePrisms, _2, _3, _Just)
import Data.List (sort)
import Freer (Reflective, lmap)
import qualified Freer as Reflective
import GHC.Generics (Generic)
import Test.QuickCheck (Arbitrary (..), genericShrink)

-- From SmartCheck

data Heap a
  = Node a (Heap a) (Heap a)
  | Empty
  deriving (Eq, Ord, Show, Read, Generic)

makePrisms ''Heap

empty :: Heap a
empty = Empty

isEmpty :: Heap a -> Bool
isEmpty Empty = True
isEmpty _ = False

unit :: a -> Heap a
unit x = Node x empty empty

size :: Heap a -> Int
size Empty = 1
size (Node _ h1 h2) = 1 + size h1 + size h2

insert :: Ord a => a -> Heap a -> Heap a
insert x h = unit x `merge` h

removeMin :: Ord a => Heap a -> Maybe (a, Heap a)
removeMin Empty = Nothing
removeMin (Node x h1 h2) = Just (x, h1 `merge` h2)

merge :: Ord a => Heap a -> Heap a -> Heap a
h1 `merge` Empty = h1
Empty `merge` h2 = h2
h1@(Node x h11 h12) `merge` h2@(Node y h21 h22)
  | x <= y = Node x (h12 `merge` h2) h11
  | otherwise = Node y (h22 `merge` h1) h21

fromList :: Ord a => [a] -> Heap a
fromList xs = merging [unit x | x <- xs]
  where
    merging [] = empty
    merging [h] = h
    merging hs = merging (sweep hs)

    sweep [] = []
    sweep [h] = [h]
    sweep (h1 : h2 : hs) = (h1 `merge` h2) : sweep hs

toList :: Heap a -> [a]
toList h = toList' [h]
  where
    toList' [] = []
    toList' (Empty : hs) = toList' hs
    toList' (Node x h1 h2 : hs) = x : toList' (h1 : h2 : hs)

toSortedList :: Ord a => Heap a -> [a]
toSortedList Empty = []
toSortedList (Node x h1 h2) = x : toList (h1 `merge` h2)

invariant :: Ord a => Heap a -> Bool
invariant Empty = True
invariant (Node x h1 h2) = x <=? h1 && x <=? h2 && invariant h1 && invariant h2

(<=?) :: Ord a => a -> Heap a -> Bool
_ <=? Empty = True
x <=? Node y _ _ = x <= y

(==?) :: Ord a => Heap a -> [a] -> Bool
h ==? xs = invariant h && sort (toList h) == sort xs

prop_ToSortedList :: Heap Int -> Bool
prop_ToSortedList (h :: Heap Int) =
  h ==? xs && xs == sort xs
  where
    xs = toSortedList h

instance Arbitrary (Heap Int) where
  arbitrary = Reflective.gen reflHeap -- Modified
  shrink = genericShrink

-- Reflective Generator

reflHeap :: Reflective (Heap Int) (Heap Int)
reflHeap = Reflective.sized (arbHeap Nothing)
  where
    arbHeap mx n =
      Reflective.frequency $
        (1, Reflective.exact Empty)
          : [ ( 7,
                do
                  my <- greaterThan mx
                  case my of
                    Nothing -> Reflective.exact Empty
                    Just y -> Node y <$> Reflective.focus (_Node . _2) arbHeap2 <*> Reflective.focus (_Node . _3) arbHeap2
                      where
                        arbHeap2 = arbHeap (Just y) (n `div` 2)
              )
              | n > 0
            ]
      where
        greaterThan v =
          lmap
            (\case Empty -> Nothing; Node x _ _ -> Just x)
            ( case v of
                Nothing -> Just <$> Reflective.focus _Just Reflective.integer
                Just hi -> Reflective.sized $ \i ->
                  if hi > i
                    then Reflective.exact Nothing
                    else Just <$> Reflective.focus _Just (Reflective.choose (hi, i))
            )