{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module SCBench where

--------------------------------------------------------------------------
-- imports

import Control.Lens (makePrisms, _1, _2, _3)
import Data.List (sort, (\\))
import Freer (FR)
import qualified Freer as FR
import Test.QuickCheck

--------------------------------------------------------------------------
-- skew heaps

data Heap a
  = Node a (Heap a) (Heap a)
  | Empty
  deriving (Eq, Ord, Show)

makePrisms ''Heap

empty :: Heap a
empty = Empty

isEmpty :: Heap a -> Bool
isEmpty Empty = True
isEmpty _ = False

unit :: a -> Heap a
unit x = Node x empty empty

size :: Heap a -> Int
size Empty = 0
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

prop_Empty :: Bool
prop_Empty =
  empty ==? ([] :: [Int])

prop_IsEmpty :: Heap Int -> Bool
prop_IsEmpty (h :: Heap Int) =
  isEmpty h == null (toList h)

prop_Unit :: Int -> Bool
prop_Unit (x :: Int) =
  unit x ==? [x]

prop_Size :: Heap Int -> Bool
prop_Size (h :: Heap Int) =
  size h == length (toList h)

prop_Insert :: Int -> Heap Int -> Bool
prop_Insert x (h :: Heap Int) =
  insert x h ==? (x : toList h)

prop_RemoveMin :: Heap Int -> Property
prop_RemoveMin (h :: Heap Int) =
  cover 80 (size h > 1) "non-trivial" $
    case removeMin h of
      Nothing -> h ==? []
      Just (x, h') -> x == minimum (toList h) && h' ==? (toList h \\ [x])

prop_Merge :: Heap Int -> Heap Int -> Bool
prop_Merge h1 (h2 :: Heap Int) =
  (h1 `merge` h2) ==? (toList h1 ++ toList h2)

prop_FromList :: [Int] -> Bool
prop_FromList (xs :: [Int]) =
  fromList xs ==? xs

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
                FR.sized
                  ( \bound ->
                      if Just bound < mx
                        then FR.exact Empty
                        else do
                          y <- FR.tryFocus (_Node . _1) (reflAtLeast mx)
                          let arbHeap2 = arbHeap (Just y) (n `div` 2)
                          Node y
                            <$> FR.tryFocus (_Node . _2) arbHeap2
                            <*> FR.tryFocus (_Node . _3) arbHeap2
                  )
              )
              | n > 0
            ]

-- instance (Ord a, Arbitrary a) => Arbitrary (Heap a) where
--   arbitrary = sized (arbHeap Nothing)
--     where
--       arbHeap mx n =
--         frequency $
--           (1, return Empty)
--             : [ ( 7,
--                   do
--                     my <- arbitrary `suchThatMaybe` ((>= mx) . Just)
--                     case my of
--                       Nothing -> return Empty
--                       Just y -> Node y <$> arbHeap2 <*> arbHeap2
--                         where
--                           arbHeap2 = arbHeap (Just y) (n `div` 2)
--                 )
--                 | n > 0
--               ]

instance Arbitrary (Heap Int) where
  arbitrary = FR.gen reflHeap
  shrink v =
    let v' = FR.shrink (not . prop_ToSortedList) reflHeap v
     in [v' | v /= v']

--------------------------------------------------------------------------
-- main

return []

main :: IO ()
main = quickCheck prop_ToSortedList