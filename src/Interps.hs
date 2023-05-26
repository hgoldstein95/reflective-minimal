{-

Contains then numerous interpretations of Reflective Generators.

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

module Interps where

import Choices
  ( BitNode (..),
    BitTree,
    Bits (..),
    bit,
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
import Control.Exception (SomeException)
import Control.Lens (view, _3)
import Control.Monad (guard)
import Control.Monad.Logic (Logic, MonadLogic (interleave, (>>-)), observeAll)
import Data.Bifunctor (Bifunctor (..))
import Data.List (group, minimumBy, sort)
import Data.Maybe (fromMaybe, listToMaybe, mapMaybe, maybeToList)
import Data.Ord (comparing)
import GHC.IO (catch, evaluate)
import qualified Test.LeanCheck as LC
import Test.QuickCheck ( Args (maxSize, maxSuccess), Gen, forAll, quickCheckWith, stdArgs)
import qualified Test.QuickCheck as QC
import Reflectives

-- Interpretations

generate :: forall d c. Reflective d c -> Gen c
generate = interp
  where
    interp :: forall b a. Reflective b a -> Gen a
    interp (Return x) = pure x
    interp (Bind r f) = interpR r >>= interp . f

    interpR :: forall b a. R b a -> Gen a
    interpR (Pick xs) = QC.frequency [(w, generate x) | (w, _, x) <- xs]
    interpR (Lmap _ x) = interpR x
    interpR (Prune x) = interpR x
    interpR (ChooseInteger (lo, hi)) = QC.chooseInteger (lo, hi)
    interpR GetSize = QC.getSize
    interpR (Resize n x) = QC.resize n (interpR x)

checkClean :: Reflective a a -> a -> Bool
checkClean g v = (not . null) (interp g v)
  where
    interp :: Reflective b a -> b -> [a]
    interp (Return x) _ = return x
    interp (Bind x f) b = interpR x b >>= \y -> interp (f y) b

    interpR :: R b a -> b -> [a]
    interpR (Pick xs) b = xs >>= (\(_, _, x) -> interp x b)
    interpR (Lmap f x) b = interpR x (f b)
    interpR (Prune x) b = maybeToList b >>= \b' -> interpR x b'
    interpR _ _ = error "interpR: clean"

check :: Reflective a a -> a -> Bool
check g v = (not . null) (interp g v Nothing)
  where
    interp :: Reflective b a -> b -> Maybe Int -> [a]
    interp (Return x) _ _ = return x
    interp (Bind x f) b s = interpR x b s >>= \y -> interp (f y) b s

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

-- This corresponds to genWithWeights in the paper
weighted :: Reflective b a -> Bool -> (String -> Int) -> Gen a
weighted g inv ws = aux g ws 100
  where
    interpR :: R b a -> (String -> Int) -> Int -> Gen a
    interpR (Pick xs) w 0 = aux (view _3 (head xs)) w 0
    interpR (Pick xs) w s =
      case filter ((> 0) . fst) . maybeInv $ map (\(_, l, x) -> (maybe 1 w l, aux x w (s - 1))) xs of
        [] -> QC.oneof (map (\(_, _, x) -> aux x w (s - 1)) xs)
        gs -> QC.frequency gs
    interpR (ChooseInteger (lo, hi)) _ _ = QC.chooseInteger (lo, hi)
    interpR (Lmap _ x) w s = interpR x w s
    interpR (Prune x) w s = interpR x w s
    interpR GetSize _ _ = QC.getSize
    interpR (Resize n x) w s = QC.resize n (interpR x w s)

    maybeInv :: [(Int, d)] -> [(Int, d)]
    maybeInv x =
      if inv
        then
          let m = maximum (map fst x)
           in map (first (m -)) x
        else x

    aux :: Reflective b a -> (String -> Int) -> Int -> Gen a
    aux (Return x) _ _ = pure x
    aux (Bind x f) w s = do
      y <- interpR x w s
      aux (f y) w s

weightsFor :: Reflective a a -> [a] -> [(String, Int)]
weightsFor g =
  map (\xs -> (head xs, length xs))
    . group
    . sort
    . concat
    . mapMaybe (unparse g)

byExample :: Reflective a a -> [a] -> Gen a
byExample g xs = weighted g False (\s -> fromMaybe 0 (lookup s (weightsFor g xs)))

byExampleInv :: Reflective a a -> [a] -> Gen a
byExampleInv g xs = weighted g True (\s -> fromMaybe 0 (lookup s (weightsFor g xs)))

-- note that in the paper this appears as
-- enumerate :: Reflective b a -> [[a]]
enum :: Reflective b a -> [a]
enum = observeAll . aux
  where
    interpR :: R b a -> Logic a
    interpR (Pick xs) = foldr (interleave . aux . view _3) empty xs
    interpR (ChooseInteger (lo, hi)) = foldr (interleave . pure) empty [lo .. hi]
    interpR (Lmap _ x) = interpR x
    interpR (Prune x) = interpR x
    interpR GetSize = error "enum: GetSize"
    interpR (Resize {}) = error "enum: Resize"

    aux :: Reflective b a -> Logic a
    aux (Return x) = pure x
    aux (Bind x f) =
      interpR x >>- \y ->
        aux (f y)

lean :: Reflective b a -> [a]
lean = concat . aux
  where
    interpR :: R b a -> [[a]]
    interpR (Pick xs) = LC.concatT [zipWith (\i (_, _, x) -> aux x `LC.ofWeight` i) [1, 2 ..] xs]
    interpR (ChooseInteger (lo, hi)) = LC.concatT [map (\x -> [[x]]) [lo .. hi]]
    interpR (Lmap _ x) = interpR x
    interpR (Prune x) = interpR x
    interpR GetSize = error "lean: GetSize"
    interpR (Resize {}) = error "lean: Resize"

    aux :: Reflective b a -> [[a]]
    aux (Return x) = [[x]]
    aux (Bind x f) = LC.concatMapT (aux . f) (interpR x)

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
    aux (Return x) b _ = pure (x, b)
    aux (Bind mx f) b s = do
      (x, b') <- interpR mx b s
      aux (f x) b' s

parse :: Reflective b a -> [String] -> [(a, [String])]
parse g v = aux g v Nothing
  where
    search [] = []
    search xs = (: []) . minimumBy (comparing (length . snd)) $ xs
    -- search = take 1

    interpR :: R b a -> [String] -> Maybe Int -> [(a, [String])]
    interpR (Pick xs) st sz = search $ do
      (_, ms, x) <- xs
      case ms of
        Nothing -> aux x st sz
        Just s -> do
          case st of
            s' : ss -> do
              guard (s == s')
              aux x ss sz
            _ -> []
    interpR (ChooseInteger (lo, hi)) s _ = (,s) <$> [lo .. hi]
    interpR (Lmap _ x) b sz = interpR x b sz
    interpR (Prune x) b sz = interpR x b sz
    interpR GetSize b (Just sz) = pure (sz, b)
    interpR GetSize b _ = pure (30, b)
    interpR (Resize sz x) b _ = interpR x b (Just sz)

    aux :: Reflective b a -> [String] -> Maybe Int -> [(a, [String])]
    aux (Return x) b _ = pure (x, b)
    aux (Bind mx f) b s = do
      (x, b') <- interpR mx b s
      aux (f x) b' s

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
    aux (Return x) _ _ = pure (x, Choices.empty)
    aux (Bind mx f) b s = do
      (x, cs) <- interpR mx b s
      (y, cs') <- aux (f x) b s
      pure (y, draw cs +++ cs')

unparse :: Reflective a a -> a -> Maybe [String]
unparse rg v = snd <$> listToMaybe (aux rg v)
  where
    interpR :: R b a -> b -> [(a, [String])]
    interpR (Pick !xs) !b = do
      (_, !ms, !x) <- xs
      case ms of
        Nothing -> aux x b
        Just !l -> second (l :) <$> aux x b
    interpR (ChooseInteger _) !b = pure (b, [])
    interpR (Lmap !f !x) !b = interpR x (f b)
    interpR (Prune !x) !b = case b of
      Nothing -> []
      Just !a -> interpR x a
    interpR GetSize _ = error "unparse: GetSize"
    interpR (Resize {}) _ = error "unparse: Resize"

    aux :: Reflective b a -> b -> [(a, [String])]
    aux (Return x) _ = pure (x, [])
    aux (Bind mx f) b = do
      (x, cs) <- interpR mx b
      (y, cs') <- aux (f x) b
      pure (y, cs ++ cs')

reflect :: Reflective a a -> a -> [[String]]
reflect g = (snd <$>) . interp g
  where
    interp :: Reflective b a -> b -> [(a, [String])]
    interp (Return x) = \_ -> pure (x, [])
    interp (Bind mx f) = \b -> do
      (x, cs) <- interpR mx b
      (y, cs') <- interp (f x) b
      pure (y, cs ++ cs')

    interpR :: R b a -> b -> [(a, [String])]
    interpR (Pick xs) = \b ->
      concatMap
        ( \(_, ms, x) ->
            case ms of
              Nothing -> interp x b
              Just lbl -> (\(a, lbls) -> (a, lbl : lbls)) <$> interp x b
        )
        xs
    interpR (Lmap f x) = interpR x . f
    interpR (Prune x) = \case
      Nothing -> []
      Just !a -> interpR x a
    interpR (ChooseInteger _) = \b -> pure (b, [])
    interpR GetSize = error "unparse: GetSize"
    interpR (Resize {}) = error "unparse: Resize"

complete :: Reflective a a -> a -> IO (Maybe a)
complete g v = do
  aux g v >>= \case
    [] -> pure Nothing
    xs -> Just <$> QC.generate (QC.elements xs)
  where
    interpR :: R b a -> b -> IO [a]
    interpR (Pick xs) b = concat <$> mapM (\(_, _, x) -> aux x b) xs
    interpR (ChooseInteger (lo, hi)) _ = pure [lo .. hi] -- TODO: Check on this
    interpR (Lmap f x) b = do
      catch
        (evaluate (f b) >>= \a -> interpR x a)
        (\(_ :: SomeException) -> (: []) <$> QC.generate (generate (Bind x Return)))
    interpR (Prune x) b = case b of
      Nothing -> pure []
      Just a -> interpR x a
    interpR GetSize _ = error "complete: GetSize"
    interpR (Resize {}) _ = error "complete: Resize"

    aux :: Reflective b a -> b -> IO [a]
    aux (Return x) _ = pure [x]
    aux (Bind mx f) b = do
      xs <- interpR mx b
      concat <$> mapM (\x -> aux (f x) b) xs

-- Other Functions

-- example for slides
containsOne :: Tree -> Bool
containsOne Leaf = False
containsOne (Node _ 1 _) = True
containsOne (Node l _ r) = containsOne l || containsOne r

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

validate :: Show a => Reflective a a -> IO ()
validate g =
  quickCheckWith
    (stdArgs {maxSuccess = 1000, maxSize = 30})
    (forAll (generate g) (check g))

validateChoice :: (Eq a, Show a) => Reflective a a -> IO ()
validateChoice g =
  quickCheckWith
    (stdArgs {maxSuccess = 1000})
    (forAll (generate g) $ \x -> all ((== Just x) . regen g . flatten) (choices g x))

validateParse :: (Eq a, Show a) => Reflective a a -> IO ()
validateParse g =
  quickCheckWith
    (stdArgs {maxSuccess = 10000})
    (forAll (generate g) $ \x -> all ((== x) . fst . head . filter (null . snd) . parse g) (unparse g x))
