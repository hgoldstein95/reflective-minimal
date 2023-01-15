{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
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

module Freer2 where

import BidirectionalProfunctors (Profmonad)
import Bits
  ( BitTree,
    Bits (..),
    bit,
    bitsToInt,
    draw,
    dropDraws,
    flatten,
    listBits,
    swapBits,
    zeroDraws,
    (+++),
  )
import qualified Bits as BitTree
import Control.Exception (SomeException)
import Control.Lens (Getting, makePrisms, over, preview, view, _1, _2, _3)
import Control.Monad (ap, guard, (>=>))
import Control.Monad.Logic (Logic, MonadLogic ((>>-)), observeAll)
import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (asum)
import Data.List (group, nub, sort)
import Data.Maybe (fromMaybe, listToMaybe)
import Data.Monoid (First)
import Data.Profunctor (Profunctor (..))
import Data.Void (Void)
import GHC.IO (catch, evaluate)
import PartialProfunctors (PartialProfunctor (..))
import Test.QuickCheck (Gen)
import qualified Test.QuickCheck as QC

-- Core Definitions

type Weight = Rational

data Freer2 f b a where
  Return :: a -> Freer2 f b a
  Bind :: f b a -> (a -> Freer2 f b c) -> Freer2 f b c

type FR b a = Freer2 Refl b a

data Refl b a where
  Pick :: [(Int, Maybe String, FR b a)] -> Refl b a
  Lmap :: (c -> d) -> FR d a -> Refl c a
  InternaliseMaybe :: FR b a -> Refl (Maybe b) a

-- Typeclass Instances Combinators

instance Functor (Freer2 f b) where
  fmap f (Return x) = Return (f x)
  fmap f (Bind u g) = Bind u (fmap f . g)

instance Applicative (Freer2 f b) where
  pure = return
  (<*>) = ap

instance Monad (Freer2 f b) where
  return = Return
  Return x >>= f = f x
  Bind u g >>= f = Bind u (g >=> f)

instance Profunctor (Freer2 Refl) where
  dimap _ g (Return a) = Return (g a)
  dimap f g x = Bind (Lmap f (g <$> x)) Return

instance Profmonad (Freer2 Refl)

instance PartialProfunctor (Freer2 Refl) where
  internaliseMaybe x = Bind (InternaliseMaybe x) Return

comap :: (u -> Maybe u') -> FR u' v -> FR u v
comap fn = dimap' fn id
  where
    dimap' :: (u -> Maybe u') -> (v -> v') -> FR u' v -> FR u v'
    dimap' f g = dimap f g . internaliseMaybe

getbits :: Int -> FR b Int
getbits w =
  Bind
    ( Pick
        [(1, Just (show (bitsToInt i)), pure (bitsToInt i)) | i <- listBits w]
    )
    Return

pick :: [(Int, String, FR b a)] -> FR b a
pick xs = Bind (Pick (map (over _2 Just) xs)) Return

frequency :: [(Int, FR b a)] -> FR b a
frequency xs = Bind (Pick (map (\(w, g) -> (w, Nothing, g)) xs)) Return

labelled :: [(String, FR b a)] -> FR b a
labelled xs = Bind (Pick (map (\(s, g) -> (1, Just s, g)) xs)) Return

oneof :: [FR b a] -> FR b a
oneof xs = Bind (Pick (map (1,Nothing,) xs)) Return

exact :: Eq v => v -> FR v v
exact x = comap (\y -> if y == x then Just y else Nothing) (pure x)

choose :: (Int, Int) -> FR Int Int
choose (lo, hi) = labelled [(show i, exact i) | i <- [lo .. hi]]

fwd :: FR c a -> FR Void a
fwd = lmap (\case {})

tryFocus :: Getting (First u') s u' -> FR u' v -> FR s v
tryFocus = comap . preview

focus :: Getting b s b -> FR b c -> FR s c
focus = lmap . view

-- Interpretations

gen :: FR b a -> Gen a
gen = aux
  where
    aux' (Pick xs) = QC.frequency (map (\(w, _, x) -> (w, aux x)) xs)
    aux' (Lmap _ x) = aux x
    aux' (InternaliseMaybe x) = aux x

    aux :: FR b a -> Gen a
    aux (Return x) = pure x
    aux (Bind x f) = do
      y <- aux' x
      aux (f y)

weighted :: FR b a -> (String -> Int) -> Gen a
weighted = aux
  where
    aux' (Pick xs) w = QC.frequency (map (\(_, s, x) -> (maybe 1 w s, aux x w)) xs)
    aux' (Lmap _ x) w = aux x w
    aux' (InternaliseMaybe x) w = aux x w

    aux :: FR b a -> (String -> Int) -> Gen a
    aux (Return x) _ = pure x
    aux (Bind x f) w = do
      y <- aux' x w
      aux (f y) w

weights :: FR a a -> [a] -> [(String, Int)]
weights g =
  map (\xs -> (head xs, length xs))
    . group
    . sort
    . head
    . concatMap (unparse g)

byExample :: FR a a -> [a] -> Gen a
byExample g xs = weighted g (\s -> fromMaybe 0 (lookup s (weights g xs)))

enum :: FR b a -> [a]
enum = observeAll . aux
  where
    aux' (Pick xs) = asum (map (aux . view _3) xs)
    aux' (Lmap _ x) = aux x
    aux' (InternaliseMaybe x) = aux x

    aux :: FR b a -> Logic a
    aux (Return x) = pure x
    aux (Bind x f) =
      aux' x >>- \y ->
        aux (f y)

regen :: FR b a -> Bits -> Maybe a
regen rg cs = listToMaybe (fst <$> aux rg (unBits cs))
  where
    aux' (Pick xs) b = do
      let numBits = ceiling (logBase 2 (fromIntegral (length xs) :: Double))
      (bs, (_, _, x)) <- zip (listBits numBits) xs
      guard (unBits bs == take numBits b)
      (y, bs') <- aux x (drop numBits b)
      pure (y, bs')
    aux' (Lmap _ x) b = aux x b
    aux' (InternaliseMaybe x) b = aux x b

    aux :: FR b a -> [Bool] -> [(a, [Bool])]
    aux (Return x) b = pure (x, b)
    aux (Bind mx f) b = do
      (x, b') <- aux' mx b
      aux (f x) b'

parse :: FR b a -> [String] -> [(a, [String])]
parse = aux
  where
    aux' (Pick xs) (s' : ss) = do
      (_, ms, x) <- xs
      case ms of
        Nothing -> aux x (s' : ss)
        Just s -> do
          guard (s == s')
          aux x ss
    aux' (Pick _) [] = []
    aux' (Lmap _ x) b = aux x b
    aux' (InternaliseMaybe x) b = aux x b

    aux :: FR b a -> [String] -> [(a, [String])]
    aux (Return x) b = pure (x, b)
    aux (Bind mx f) b = do
      (x, b') <- aux' mx b
      aux (f x) b'

bits :: FR a a -> a -> [Bits]
bits rg v = Bits . snd <$> aux rg v
  where
    aux' (Pick xs) b = do
      let numBits = ceiling (logBase 2 (fromIntegral (length xs) :: Double))
      (bs, (_, _, x)) <- zip (listBits numBits) xs
      (y, bs') <- aux x b
      pure (y, unBits bs ++ bs')
    aux' (Lmap f x) b = aux x (f b)
    aux' (InternaliseMaybe x) b = case b of
      Nothing -> []
      Just a -> aux x a

    aux :: FR b a -> b -> [(a, [Bool])]
    aux (Return x) _ = pure (x, [])
    aux (Bind mx f) b = do
      (x, cs) <- aux' mx b
      (y, cs') <- aux (f x) b
      pure (y, cs ++ cs')

choices :: FR a a -> a -> [BitTree]
choices rg v = snd <$> aux rg v
  where
    aux' (Pick xs) b = do
      let numBits = ceiling (logBase 2 (fromIntegral (length xs) :: Double))
      (bs, (_, _, x)) <- zip (listBits numBits) xs
      (y, bs') <- aux x b
      pure (y, foldr ((+++) . bit) BitTree.empty (unBits bs) +++ bs')
    aux' (Lmap f x) b = aux x (f b)
    aux' (InternaliseMaybe x) b = case b of
      Nothing -> []
      Just a -> aux x a

    aux :: FR b a -> b -> [(a, BitTree)]
    aux (Return x) _ = pure (x, BitTree.empty)
    aux (Bind mx f) b = do
      (x, cs) <- aux' mx b
      (y, cs') <- aux (f x) b
      pure (y, draw cs +++ cs')

unparse :: FR a a -> a -> [[String]]
unparse rg v = snd <$> aux rg v
  where
    aux' (Pick xs) b = do
      (_, ms, x) <- xs
      case ms of
        Nothing -> aux x b
        Just s -> second (s :) <$> aux x b
    aux' (Lmap f x) b = aux x (f b)
    aux' (InternaliseMaybe x) b = case b of
      Nothing -> []
      Just a -> aux x a

    aux :: FR b a -> b -> [(a, [String])]
    aux (Return x) _ = pure (x, [])
    aux (Bind mx f) b = do
      (x, cs) <- aux' mx b
      (y, cs') <- aux (f x) b
      pure (y, cs ++ cs')

complete :: FR a a -> a -> IO (Maybe a)
complete g v = do
  aux g v 30 >>= \case
    [] -> pure Nothing
    xs -> Just <$> QC.generate (QC.elements xs)
  where
    aux' (Pick xs) b s = concat <$> mapM (\(_, _, x) -> aux x b s) xs
    aux' (Lmap f x) b s = do
      catch
        (evaluate (f b) >>= \a -> aux x a s)
        (\(_ :: SomeException) -> (: []) <$> QC.generate (QC.resize s (gen x)))
    aux' (InternaliseMaybe x) b s = case b of
      Nothing -> pure []
      Just a -> aux x a s

    aux :: FR b a -> b -> Int -> IO [a]
    aux (Return x) _ _ = pure [x]
    aux (Bind mx f) b s = do
      xs <- aux' mx b s
      concat <$> mapM (\x -> aux (f x) b s) xs

-- Examples

data Tree = Leaf | Node Tree Int Tree
  deriving (Show, Eq, Ord)

makePrisms ''Tree

height :: Tree -> Int
height Leaf = 0
height (Node l _ r) = 1 + max (height l) (height r)

unbalanced :: Tree -> Bool
unbalanced Leaf = False
unbalanced (Node l _ r) =
  unbalanced l || unbalanced r || abs (height l - height r) > 1

nodeValue :: Tree -> Maybe Int
nodeValue (Node _ x _) = Just x
nodeValue _ = Nothing

nodeLeft :: Tree -> Maybe Tree
nodeLeft (Node l _ _) = Just l
nodeLeft _ = Nothing

nodeRight :: Tree -> Maybe Tree
nodeRight (Node _ _ r) = Just r
nodeRight _ = Nothing

weirdTree :: FR Tree Tree
weirdTree = aux (10 :: Int)
  where
    aux n
      | n == 0 = exact Leaf
      | otherwise = do
          oneof
            [ exact Leaf,
              do
                x <- comap nodeValue (choose (1, 10))
                l <- comap nodeLeft (aux (n - 1))
                r <- comap nodeRight (aux (n - 1))
                pure (Node l x r),
              exact (Node Leaf 2 Leaf)
            ]

bstFwd :: FR Void Tree
bstFwd = aux (1, 10)
  where
    aux (lo, hi)
      | lo > hi = return Leaf
      | otherwise = do
          oneof
            [ return Leaf,
              do
                x <- fwd (choose (lo, hi))
                l <- fwd (aux (lo, x - 1))
                r <- fwd (aux (x + 1, hi))
                return (Node l x r)
            ]

bst :: FR Tree Tree
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
                  x <- tryFocus (_Node . _2) (choose (lo, hi))
                  l <- tryFocus (_Node . _1) (aux (lo, x - 1))
                  r <- tryFocus (_Node . _3) (aux (x + 1, hi))
                  exact (Node l x r)
              )
            ]

hypoTree :: FR Tree Tree
hypoTree = do
  c <- getbits 1
  if c /= 0
    then do
      l <- comap nodeLeft hypoTree
      r <- comap nodeRight hypoTree
      exact (Node l 0 r)
    else exact Leaf

data Expr
  = Num Int
  | Add Expr Expr
  | Mul Expr Expr
  deriving (Show, Eq, Ord)

makePrisms ''Expr

expression :: FR Expr Expr
expression = expr (10 :: Int)
  where
    expr n
      | n <= 1 = term n
      | otherwise =
          oneof
            [ do
                x <- tryFocus (_Add . _1) (term (n `div` 2))
                y <- token "+" *> tryFocus (_Add . _2) (expr (n `div` 2))
                pure (Add x y),
              term n
            ]
    term n
      | n <= 1 = factor n
      | otherwise =
          oneof
            [ do
                x <- tryFocus (_Mul . _1) (factor (n `div` 2))
                y <- token "*" *> tryFocus (_Mul . _2) (term (n `div` 2))
                pure (Mul x y),
              factor n
            ]
    factor n
      | n <= 1 = Num <$> tryFocus _Num (choose (1, 10))
      | otherwise =
          oneof
            [ Num <$> tryFocus _Num (choose (1, 10)),
              token "(" *> expr (n - 1) <* token ")"
            ]
    token s = labelled [(s, pure ())]

shrink :: (a -> Bool) -> FR a a -> a -> a
shrink p g =
  fromMaybe (error "shrink: no solution")
    . regen g
    . flatten
    . head
    . applyShrinker swapBits
    . applyShrinker zeroDraws
    . applyShrinker dropDraws
    . choices g
  where
    applyShrinker :: (BitTree -> [BitTree]) -> [BitTree] -> [BitTree]
    applyShrinker s ts =
      let ts' = take 1 . sort . filter (any p . regen g . flatten) . concatMap s $ ts
       in case ts' of
            [] -> ts
            _ -> applyShrinker s ts'

main :: IO ()
main = do
  print (nub $ bits weirdTree (Node Leaf 1 (Node Leaf 2 Leaf)))
  print =<< QC.generate (gen weirdTree)
  print =<< QC.generate (gen bstFwd)
  let cs = head . nub $ bits bst (Node Leaf 1 (Node Leaf 2 Leaf))
  print cs
  print (regen bst cs)
  let ss = head . nub $ unparse bst (Node Leaf 1 (Node Leaf 2 Leaf))
  print ss
  print (parse bst ss)
  let n l = Node l 0
  print $ bits hypoTree (n (n Leaf (n (n Leaf (n (n Leaf Leaf) Leaf)) Leaf)) (n (n Leaf (n (n Leaf (n Leaf Leaf)) (n Leaf Leaf))) Leaf))
  print $ bits hypoTree (n Leaf (n (n Leaf (n (n Leaf (n Leaf Leaf)) (n Leaf Leaf))) Leaf))
  print $ bits hypoTree (n Leaf (n (n Leaf Leaf) Leaf))
  print $ bits hypoTree (n Leaf (n Leaf (n Leaf Leaf)))
  print $ choices hypoTree (n Leaf (n Leaf (n Leaf Leaf)))
  print $ choices bst (Node (Node Leaf 1 Leaf) 3 (Node Leaf 5 Leaf))
  mapM_ print $ zeroDraws $ head $ choices bst (Node (Node Leaf 1 Leaf) 3 (Node Leaf 5 Leaf))
  let tii = (,,) <$> focus _1 bst <*> focus _2 (choose (1, 10)) <*> focus _3 (choose (1, 10)) :: FR (Tree, Int, Int) (Tree, Int, Int)
  mapM_ print $ take 20 $ nub $ enum tii
  print $ map fst $ filter (null . snd) $ parse expression (words "( 1 + 2 ) * ( 3 + 3 * 4 )")
  print $ take 3 $ map concat $ unparse expression (Mul (Add (Num 1) (Num 2)) (Num 3))
  let _hole_ = undefined
  print =<< complete bst (Node _hole_ 5 _hole_)
  print =<< complete bst (Node (Node _hole_ 2 Leaf) 5 (Node _hole_ 7 _hole_))
  print =<< QC.generate (byExample expression [Mul (Num 1) (Num 2), Mul (Num 3) (Num 4)])

  let t = n (n Leaf (n (n Leaf (n (n Leaf Leaf) Leaf)) Leaf)) (n (n Leaf (n (n Leaf (n Leaf Leaf)) (n Leaf Leaf))) Leaf)
  print $ shrink unbalanced hypoTree t