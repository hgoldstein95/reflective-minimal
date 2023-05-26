{-

All the core definitions for Reflective Generators, a DSL for creating them, and
some small examples.

-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns  #-}

module Reflectives where

import Choices ( bitsToInt, listBits )
import Control.Lens (Getting, makePrisms, over, preview, _1, _2, _3, _head, _tail)
import Control.Monad (ap, (>=>))
import Data.Char (chr, ord)
import Data.List (transpose)
import Data.Monoid (First)
import Data.Void (Void)
import GHC.Generics (Generic)
import Test.QuickCheck ( Arbitrary, genericShrink)
import Test.QuickCheck.Arbitrary.Generic (genericArbitrary)
import qualified Test.QuickCheck as QC

-- Core Definitions

data Freer f a where
  Return :: a -> Freer f a
  Bind :: f a -> (a -> Freer f c) -> Freer f c

type Choice = Maybe String

type Weight = Int

data R b a where
  Pick :: [(Weight, Choice, Reflective b a)] -> R b a
  Lmap :: (c -> d) -> R d a -> R c a
  Prune :: R b a -> R (Maybe b) a
  ChooseInteger :: (Integer, Integer) -> R Integer Integer
  GetSize :: R b Int
  Resize :: Int -> R b a -> R b a

type Reflective b = Freer (R b)

-- Typeclass Instances Combinators

instance Functor (Reflective b) where
  fmap f (Return x) = Return (f x)
  fmap f (Bind u g) = Bind u (fmap f . g)

instance Applicative (Reflective b) where
  pure = return
  (<*>) = ap

instance Monad (Reflective b) where
  return = Return
  Return x >>= f = f x
  Bind u g >>= f = Bind u (g >=> f)

dimap :: (c -> d) -> (a -> b) -> Reflective d a -> Reflective c b
dimap _ g (Return a) = Return (g a)
dimap f g (Bind x h) = Bind (Lmap f x) (dimap f g . h)

lmap :: (c -> d) -> Reflective d a -> Reflective c a
lmap f = dimap f id

prune :: Reflective b a -> Reflective (Maybe b) a
prune (Return a) = Return a
prune (Bind x f) = Bind (Prune x) (prune . f)

comap :: (a -> Maybe b) -> Reflective b v -> Reflective a v
comap f = lmap f . prune

getbits :: Int -> Reflective b Int
getbits w =
  Bind
    ( Pick
        [(1, Just (show (bitsToInt i)), pure (bitsToInt i)) | i <- listBits w]
    )
    Return

pick :: [(Int, String, Reflective b a)] -> Reflective b a
pick xs = Bind (Pick (map (over _2 Just) xs)) Return

frequency :: [(Int, Reflective b a)] -> Reflective b a
frequency xs = Bind (Pick (map (\(w, g) -> (w, Nothing, g)) xs)) Return

labelled :: [(String, Reflective b a)] -> Reflective b a
labelled xs = Bind (Pick (map (\(s, g) -> (1, Just s, g)) xs)) Return

oneof :: [Reflective b a] -> Reflective b a
oneof xs = Bind (Pick (map (1,Nothing,) xs)) Return

exact :: Eq v => v -> Reflective v v
exact x = comap (\y -> if y == x then Just y else Nothing) $ oneof [pure x]

choose :: (Int, Int) -> Reflective Int Int
choose (lo, hi) = labelled [(show i, exact i) | i <- [lo .. hi]]

chooseInteger :: (Integer, Integer) -> Reflective Integer Integer
chooseInteger p = Bind (ChooseInteger p) Return

integer :: Reflective Int Int
integer = sized $ \n -> labelled [(show i, exact i) | i <- concat (transpose [[0 .. n], reverse [-n .. -1]])]

char :: Reflective Char Char
char = sized $ \n -> labelled [(show i, exact (chr i)) | i <- [ord 'a' .. ord 'a' + n]]

alphaNum :: Reflective Char Char
alphaNum = labelled [(show c, exact c) | c <- ['a', 'b', 'c', '1', '2', '3']]

bool :: Reflective Bool Bool
bool = oneof [exact True, exact False]

vectorOf :: Eq a => Int -> Reflective a a -> Reflective [a] [a]
vectorOf 0 _ = exact []
vectorOf n g = do
  x <- focus _head g
  xs <- focus _tail (vectorOf (n - 1) g)
  exact (x : xs)

listOf :: Eq a => Reflective a a -> Reflective [a] [a]
listOf g = sized aux
  where
    aux 0 = exact []
    aux n =
      frequency
        [ (1, exact []),
          ( n,
            do
              x <- focus _head g
              xs <- focus _tail (aux (n - 1))
              exact (x : xs)
          )
        ]

nonEmptyListOf :: Eq a => Reflective a a -> Reflective [a] [a]
nonEmptyListOf g = do
  x <- focus _head g
  xs <- focus _tail (sized aux)
  exact (x : xs)
  where
    aux 0 = exact []
    aux n =
      frequency
        [ (1, exact []),
          ( n,
            do
              x <- focus _head g
              xs <- focus _tail (aux (n - 1))
              exact (x : xs)
          )
        ]

fwd :: Reflective c a -> Reflective Void a
fwd = lmap (\case {})

focus :: Getting (First u') s u' -> Reflective u' v -> Reflective s v
focus = comap . preview

resize :: Int -> Reflective b a -> Reflective b a
resize _ (Return x) = Return x
resize w (Bind x f) = Bind (Resize w x) (resize w . f)

sized :: (Int -> Reflective b a) -> Reflective b a
sized = Bind GetSize

-- Examples

data Tree = Leaf | Node Tree Int Tree
  deriving (Show, Eq, Ord, Generic)

instance Arbitrary Tree where
  arbitrary = genericArbitrary
  shrink = genericShrink

makePrisms ''Tree

nodeValue :: Tree -> Maybe Int
nodeValue (Node _ x _) = Just x
nodeValue _ = Nothing

nodeLeft :: Tree -> Maybe Tree
nodeLeft (Node l _ _) = Just l
nodeLeft _ = Nothing

nodeRight :: Tree -> Maybe Tree
nodeRight (Node _ _ r) = Just r
nodeRight _ = Nothing

bstFwd :: (Int, Int) -> Reflective Void Tree
bstFwd (lo, hi) | lo > hi = return Leaf
bstFwd (lo, hi) =
  frequency
    [ ( 1, return Leaf),
      ( 5, do
        x <- fwdOnly (choose (lo, hi))
        l <- fwdOnly (bstFwd (lo, x - 1))
        r <- fwdOnly (bstFwd (x + 1, hi))
        return (Node l x r) ) ]
  where
    fwdOnly = lmap (\ x -> case x of)

bst :: Reflective Tree Tree
bst = aux (1, 10)
  where
    aux (lo, hi)
      | lo > hi = exact Leaf
      | otherwise = do
          labelled
            [ ( "leaf",
                exact Leaf
              ),
              ( "node",
                do
                  x <- focus (_Node . _2) (choose (lo, hi))
                  l <- focus (_Node . _1) (aux (lo, x - 1))
                  r <- focus (_Node . _3) (aux (x + 1, hi))
                  exact (Node l x r)
              )
            ]

hypoTree :: Reflective Tree Tree
hypoTree =
  oneof
    [ exact Leaf,
      do
        l <- comap nodeLeft hypoTree
        r <- comap nodeRight hypoTree
        exact (Node l 0 r)
    ]

data UnLabTree = UnLabLeaf | UnLabBranch UnLabTree UnLabTree deriving (Eq, Show, Generic)

instance Arbitrary UnLabTree where
  arbitrary = genericArbitrary
  shrink = genericShrink

makePrisms ''UnLabTree

unlabelled :: Reflective UnLabTree UnLabTree
unlabelled =
  oneof
    [ exact UnLabLeaf,
      UnLabBranch
        <$> focus (_UnLabBranch . _1) unlabelled
        <*> focus (_UnLabBranch . _2) unlabelled
    ]
