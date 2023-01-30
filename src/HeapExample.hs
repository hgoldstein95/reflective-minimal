{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module HeapExample where

--------------------------------------------------------------------------
-- imports

import Control.Lens (makePrisms, _2, _3, _Just)
import Data.List (sort)
import Data.Profunctor (lmap)
import Freer (FR)
import qualified Freer as FR
import GHC.Generics (Generic)
import Test.QuickCheck (Arbitrary (..), genericShrink)

--------------------------------------------------------------------------
-- skew heaps

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

--------------------------------------------------------------------------
-- specification

invariant :: Ord a => Heap a -> Bool
invariant Empty = True
invariant (Node x h1 h2) = x <=? h1 && x <=? h2 && invariant h1 && invariant h2

(<=?) :: Ord a => a -> Heap a -> Bool
_ <=? Empty = True
x <=? Node y _ _ = x <= y

(==?) :: Ord a => Heap a -> [a] -> Bool
h ==? xs = invariant h && sort (toList h) == sort xs

--------------------------------------------------------------------------
-- properties

prop_ToSortedList :: Heap Int -> Bool
prop_ToSortedList (h :: Heap Int) =
  h ==? xs && xs == sort xs
  where
    xs = toSortedList h

--------------------------------------------------------------------------
-- generators

reflAtLeast :: Maybe Int -> FR Int Int
reflAtLeast Nothing = FR.integer
reflAtLeast (Just hi) = FR.sized (\mx -> FR.choose (hi, mx))

reflHeap :: FR (Heap Int) (Heap Int)
reflHeap = FR.sized (arbHeap Nothing)
  where
    arbHeap mx n =
      FR.frequency $
        (1, FR.exact Empty)
          : [ ( 7,
                do
                  my <- greaterThan mx
                  case my of
                    Nothing -> FR.exact Empty
                    Just y -> Node y <$> FR.tryFocus (_Node . _2) arbHeap2 <*> FR.tryFocus (_Node . _3) arbHeap2
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
                Nothing -> Just <$> FR.tryFocus _Just FR.integer
                Just hi -> FR.sized $ \i ->
                  if hi > i
                    then FR.exact Nothing
                    else Just <$> FR.tryFocus _Just (FR.choose (hi, i))
            )

instance Arbitrary (Heap Int) where
  arbitrary = FR.gen reflHeap
  shrink = genericShrink