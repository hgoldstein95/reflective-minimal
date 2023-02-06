{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module FreerChurch where

import Choices
  ( BitNode (..),
    BitTree,
    Bits (..),
    bit,
    bitsToInt,
    bitsToInteger,
    draw,
    flatten,
    integerToBits,
    listBits,
    subChoices,
    swapBits,
    tree,
    zeroDraws,
    (+++),
  )
import qualified Choices
import Control.Applicative (empty)
import Control.Lens (Getting, over, preview, _2, _head, _tail)
import Control.Monad (guard, join)
import Control.Monad.Free.Church
import Data.Char (chr, ord)
import Data.List (sort, transpose)
import Data.Maybe (fromMaybe, listToMaybe, maybeToList)
import Data.Monoid (First)
import Data.Void (Void)
import Test.QuickCheck (Gen)
import qualified Test.QuickCheck as QC

-- Core Definitions

type Choice = Maybe String

type Weight = Int

data R b a where
  Pick :: [(Weight, Choice, Reflective b a)] -> R b a
  Lmap :: (c -> d) -> R d a -> R c a
  Prune :: R b a -> R (Maybe b) a
  ChooseInteger :: (Integer, Integer) -> R Integer Integer
  GetSize :: R b Int
  Resize :: Int -> R b a -> R b a

type Reflective b = F (R b)

-- Typeclass Instances Combinators

instance Functor (R b) where
  fmap f (Pick xs) = Pick (map (\(w, c, g) -> (w, c, fmap f g)) xs)
  fmap f (Lmap g h) = Lmap g (f <$> h)
  fmap f (Prune g) = Prune (fmap f g)
  fmap f (ChooseInteger p) = Pick [(1, Nothing, f <$> lift (ChooseInteger p))]
  fmap f GetSize = Pick [(1, Nothing, f <$> lift GetSize)]
  fmap f (Resize n g) = Resize n (fmap f g)

dimap :: (c -> d) -> (a -> b) -> Reflective d a -> Reflective c b
dimap f g m = F $ \ret bnd ->
  runF m (ret . g) (bnd . Lmap f)

-- dimap f g  = Bind (Lmap f x) (dimap f g . h)

lmap :: (c -> d) -> Reflective d a -> Reflective c a
lmap f = dimap f id

prune :: Reflective b a -> Reflective (Maybe b) a
prune m = F $ \ret bnd -> runF m ret (bnd . Prune)

comap :: (a -> Maybe b) -> Reflective b v -> Reflective a v
comap f = lmap f . prune

lift :: R b a -> Reflective b a
lift r = F $ \ret bnd -> bnd (ret <$> r)

getbits :: Int -> Reflective b Int
getbits w =
  lift
    ( Pick
        [(1, Just (show (bitsToInt i)), pure (bitsToInt i)) | i <- listBits w]
    )

pick :: [(Int, String, Reflective b a)] -> Reflective b a
pick xs = lift (Pick (map (over _2 Just) xs))

frequency :: [(Int, Reflective b a)] -> Reflective b a
frequency xs = lift (Pick (map (\(w, g) -> (w, Nothing, g)) xs))

labelled :: [(String, Reflective b a)] -> Reflective b a
labelled xs = lift (Pick (map (\(s, g) -> (1, Just s, g)) xs))

oneof :: [Reflective b a] -> Reflective b a
oneof xs = lift (Pick (map (1,Nothing,) xs))

exact :: Eq v => v -> Reflective v v
exact x = comap (\y -> if y == x then Just y else Nothing) $ oneof [pure x]

choose :: (Int, Int) -> Reflective Int Int
choose (lo, hi) = labelled [(show i, exact i) | i <- [lo .. hi]]

chooseInteger :: (Integer, Integer) -> Reflective Integer Integer
chooseInteger p = lift (ChooseInteger p)

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
resize w m = F $ \ret bnd -> runF m ret (bnd . Resize w)

getSize :: Reflective b Int
getSize = lift GetSize

sized :: (Int -> Reflective b a) -> Reflective b a
sized = (getSize >>=)

-- Interpretations

gen :: forall d c. Reflective d c -> Gen c
gen = interp
  where
    interp :: forall b a. Reflective b a -> Gen a
    interp m = runF m pure (join . interpR)

    interpR :: forall b a. R b a -> Gen a
    interpR (Pick xs) = QC.frequency [(w, gen x) | (w, _, x) <- xs]
    interpR (Lmap _ x) = interpR x
    interpR (Prune x) = interpR x
    interpR (ChooseInteger (lo, hi)) = QC.chooseInteger (lo, hi)
    interpR GetSize = QC.getSize
    interpR (Resize n x) = QC.resize n (interpR x)

check :: Reflective a a -> a -> Bool
check g v = (not . null) (interp g v Nothing)
  where
    interp :: Reflective b a -> b -> Maybe Int -> [a]
    interp m b s = runF m pure (\r -> join (interpR r b s))

    interpR :: R b a -> b -> Maybe Int -> [a]
    interpR (Pick xs) b s = concat [interp x b s | (_, _, x) <- xs]
    interpR (Lmap f x) b s = interpR x (f b) s
    interpR (Prune x) b s = maybeToList b >>= \b' -> interpR x b' s
    interpR (ChooseInteger (lo, hi)) b _
      | lo <= b && b <= hi = pure b
      | otherwise = empty
    interpR GetSize _ (Just s) = return s
    interpR GetSize _ Nothing = pure 30
    interpR (Resize s x) b _ = interpR x b (Just s)

choices :: Reflective a a -> a -> [BitTree]
choices rg v = snd <$> aux rg v Nothing
  where
    interpR :: R b a -> b -> Maybe Int -> [(a, BitTree)]
    interpR (Pick xs) b s = do
      let numBits = ceiling (logBase 2 (fromIntegral (length xs) :: Double))
      (bs, (_, _, x)) <- zip (listBits numBits) xs
      (y, bs') <- aux x b s
      pure (y, foldr ((+++) . bit) Choices.empty (unBits bs) +++ bs')
    interpR (ChooseInteger (lo, hi)) b _ =
      [(b, tree . map Bit $ integerToBits (lo, hi) b) | not (b < lo || b > hi)]
    interpR (Lmap f x) b s = interpR x (f b) s
    interpR (Prune x) b s = case b of
      Nothing -> []
      Just a -> interpR x a s
    interpR GetSize _ Nothing = pure (30, Choices.empty)
    interpR GetSize _ (Just n) = pure (n, Choices.empty)
    interpR (Resize n x) b _ = interpR x b (Just n)

    aux :: Reflective b a -> b -> Maybe Int -> [(a, BitTree)]
    aux m b s =
      runF
        m
        (\x -> pure (x, Choices.empty))
        ( \r ->
            do
              (x, cs) <- interpR r b s
              (y, cs') <- x
              pure (y, draw cs +++ cs')
        )

regen :: Reflective b a -> Bits -> Maybe a
regen rg cs = listToMaybe (fst <$> aux rg (unBits cs) Nothing)
  where
    interpR :: R b a -> [Bool] -> Maybe Int -> [(a, [Bool])]
    interpR (Pick xs) b s = do
      let numBits = ceiling (logBase 2 (fromIntegral (length xs) :: Double))
      (bs, (_, _, x)) <- zip (listBits numBits) xs
      guard (unBits bs == take numBits b)
      (y, bs') <- aux x (drop numBits b) s
      pure (y, bs')
    interpR (ChooseInteger (lo, hi)) b _ = maybeToList $ bitsToInteger (lo, hi) b
    interpR (Lmap _ x) b s = interpR x b s
    interpR (Prune x) b s = interpR x b s
    interpR GetSize b Nothing = pure (30, b)
    interpR GetSize b (Just n) = pure (n, b)
    interpR (Resize n x) b _ = interpR x b (Just n)

    aux :: Reflective b a -> [Bool] -> Maybe Int -> [(a, [Bool])]
    aux m bb s =
      runF
        m
        (curry pure)
        ( \r b -> do
            (x, b') <- interpR r b s
            x b'
        )
        bb

-- aux (Bind mx f) b s = do
--   (x, b') <- interpR mx b s
--   aux (f x) b' s

shrink :: (a -> Bool) -> Reflective a a -> a -> a
shrink p g =
  fromMaybe (error "shrink: no solution")
    . regen g
    . flatten
    . head
    . applyShrinker swapBits
    . applyShrinker zeroDraws
    . applyShrinker subChoices
    . take 1
    . choices g
  where
    applyShrinker :: (BitTree -> [BitTree]) -> [BitTree] -> [BitTree]
    applyShrinker s !ts =
      let ts' = take 1 . filter (any p . regen g . flatten) . sort . concatMap s $ ts
       in if null ts' || ts' == ts then ts else applyShrinker s ts'