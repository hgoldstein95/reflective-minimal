{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module BSTEnumExample where

import Control.Lens (_1, _2, _3)
import Data.List (find)
import Freer
import Test.LeanCheck

(>>-) :: [[a]] -> (a -> [[b]]) -> [[b]]
(>>-) = flip concatMapT

instance Listable Tree where
  tiers :: [[Tree]]
  tiers = leanBST (1, 10)
    where
      leanBST (lo, hi) | lo > hi = [[Leaf]]
      leanBST (lo, hi) =
        cons0 Leaf
          \/ ( lcchoose (lo, hi) >>- \x ->
                 leanBST (lo, x - 1) >>- \l ->
                   leanBST (x + 1, hi) >>- \r ->
                     delay [[Node l x r]]
             )

      lcchoose :: (Int, Int) -> [[Int]]
      lcchoose (lo, hi) = concatT [zipWith (\i x -> [[x]] `ofWeight` i) [0 ..] [lo .. hi]]

buggyInsert :: Int -> Tree -> Tree
buggyInsert k Leaf = Node Leaf k Leaf
buggyInsert k (Node l k' r)
  | k < k' = Node (buggyInsert k l) k' r
  | k < k' = Node (buggyInsert k l) k' r
  | otherwise = Node l k' r

mem :: Int -> Tree -> Bool
mem _ Leaf = False
mem k (Node l k' r)
  | k < k' = mem k l
  | k > k' = mem k r
  | otherwise = True

isBST :: Tree -> Bool
isBST Leaf = True
isBST (Node l k r) =
  isBST l
    && isBST r
    && all (< k) (keys l)
    && all (> k) (keys r)

keys :: Tree -> [Int]
keys Leaf = []
keys (Node l k r) = keys l ++ [k] ++ keys r

prop_InsertInsert :: (Tree, Int, Int) -> Bool
prop_InsertInsert (t, k, k') =
  not (isBST t)
    || ( buggyInsert k (buggyInsert k' t)
           =~= if k == k' then buggyInsert k t else buggyInsert k' (buggyInsert k t)
       )

(=~=) :: Tree -> Tree -> Bool
t1 =~= t2 = keys t1 == keys t2

main :: IO ()
main =
  print $ fst <$> find (\(_, x) -> not (prop_InsertInsert x)) (zip [0 :: Int ..] (enum inputs))
  where
    inputs :: Reflective (Tree, Int, Int) (Tree, Int, Int) = (,,) <$> focus _1 bst <*> focus _2 (choose (-10, 10)) <*> focus _3 (choose (-10, 10))