{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Freer2 where

import BidirectionalProfunctors (Profmonad)
import Control.Lens (Getting, makePrisms, preview, view, _1, _2, _3)
import Control.Monad (ap, (>=>))
import Control.Monad.Logic (Logic, MonadLogic ((>>-)), observeAll)
import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (asum)
import Data.List (nub)
import Data.Monoid (First)
import Data.Profunctor (Profunctor (..))
import Data.Ratio (denominator, numerator)
import Data.Void (Void)
import PartialProfunctors (PartialProfunctor (..))
import Test.QuickCheck (Gen)
import qualified Test.QuickCheck as QC

type Weight = Rational

data Freer2 f b a where
  Return :: a -> Freer2 f b a
  Bind :: f b a -> (a -> Freer2 f b c) -> Freer2 f b c

type FR b a = Freer2 Refl b a

data Refl b a where
  Coin :: Weight -> Refl b Bool
  Label :: String -> FR b a -> Refl b a
  Lmap :: (c -> d) -> FR d a -> Refl c a
  InternaliseMaybe :: FR b a -> Refl (Maybe b) a

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

coin :: Weight -> FR b Bool
coin w = Bind (Coin w) Return

pick :: [FR b a] -> FR b a
pick [] = error "pick: empty list"
pick [x] = x
pick xs = do
  b <- coin (1 / fromIntegral (length xs))
  if b
    then head xs
    else pick (tail xs)

exact :: Eq v => v -> FR v v
exact x = comap (\y -> if y == x then Just y else Nothing) (pure x)

fwd :: FR c a -> FR Void a
fwd = lmap (\case {})

fix :: ((i -> FR b a) -> i -> FR b a) -> i -> FR b a
fix f = f (fix f)

label :: String -> FR b a -> FR b a
label s x = Bind (Label s x) Return

gen :: FR b a -> Gen a
gen = aux
  where
    aux' :: Refl b a -> Gen a
    aux' (Coin w) = (< numerator w) <$> QC.choose (0, denominator w)
    aux' (Lmap _ x) = aux x
    aux' (InternaliseMaybe x) = aux x
    aux' (Label _ x) = aux x

    aux :: FR b a -> Gen a
    aux (Return x) = pure x
    aux (Bind x f) = do
      y <- aux' x
      aux (f y)

enum :: FR b a -> [a]
enum = observeAll . aux
  where
    aux' :: Refl b a -> Logic a
    aux' (Coin w) = (< numerator w) <$> asum (map pure [0 .. denominator w])
    aux' (Lmap _ x) = aux x
    aux' (InternaliseMaybe x) = aux x
    aux' (Label _ x) = aux x

    aux :: FR b a -> Logic a
    aux (Return x) = pure x
    aux (Bind x f) =
      aux' x >>- \y ->
        aux (f y)

regen :: FR b a -> [Bool] -> [a]
regen rg cs = fst <$> aux rg cs
  where
    aux' :: Refl b a -> [Bool] -> [(a, [Bool])]
    aux' (Coin _) [] = []
    aux' (Coin _) (b : bs) = pure (b, bs)
    aux' (Lmap _ x) b = aux x b
    aux' (InternaliseMaybe x) b = aux x b
    aux' (Label _ x) b = aux x b

    aux :: FR b a -> [Bool] -> [(a, [Bool])]
    aux (Return x) b = pure (x, b)
    aux (Bind mx f) b = do
      (x, b') <- aux' mx b
      aux (f x) b'

parse :: FR b a -> [String] -> [(a, [String])]
parse = aux
  where
    aux' :: Refl b a -> [String] -> [(a, [String])]
    aux' (Coin _) b = [(True, b), (False, b)]
    aux' (Lmap _ x) b = aux x b
    aux' (InternaliseMaybe x) b = aux x b
    aux' (Label s x) (s' : ss)
      | s == s' = aux x ss
      | otherwise = []
    aux' (Label _ _) [] = []

    aux :: FR b a -> [String] -> [(a, [String])]
    aux (Return x) b = pure (x, b)
    aux (Bind mx f) b = do
      (x, b') <- aux' mx b
      aux (f x) b'

bits :: FR a a -> a -> [[Bool]]
bits rg v = snd <$> aux rg v
  where
    aux' :: Refl b a -> b -> [(a, [Bool])]
    aux' (Coin _) _ = [(True, [True]), (False, [False])]
    aux' (Lmap f x) b = aux x (f b)
    aux' (InternaliseMaybe x) b = case b of
      Nothing -> []
      Just a -> aux x a
    aux' (Label _ x) b = aux x b

    aux :: FR b a -> b -> [(a, [Bool])]
    aux (Return x) _ = pure (x, [])
    aux (Bind mx f) b = do
      (x, cs) <- aux' mx b
      (y, cs') <- aux (f x) b
      pure (y, cs ++ cs')

type Choices = [Choice]

data Choice = Draw Choices | Flip Bool
  deriving (Show, Eq, Ord)

(+++) :: Choices -> Choices -> Choices
(+++) xs ys = collapse (xs ++ ys)
  where
    collapse = filter (/= Draw []) . map (\case Draw cs -> Draw (collapse cs); x -> x)

choices :: FR a a -> a -> [Choices]
choices rg v = snd <$> aux rg v
  where
    aux' :: Refl b a -> b -> [(a, Choices)]
    aux' (Coin _) _ = [(True, [Flip True]), (False, [Flip False])]
    aux' (Lmap f x) b = aux x (f b)
    aux' (InternaliseMaybe x) b = case b of
      Nothing -> []
      Just a -> aux x a
    aux' (Label _ x) b = second ((: []) . Draw) <$> aux x b

    aux :: FR b a -> b -> [(a, Choices)]
    aux (Return x) _ = pure (x, [])
    aux (Bind mx f) b = do
      (x, cs) <- aux' mx b
      (y, cs') <- aux (f x) b
      pure (y, cs +++ cs')

unparse :: FR a a -> a -> [[String]]
unparse rg v = snd <$> aux rg v
  where
    aux' :: Refl b a -> b -> [(a, [String])]
    aux' (Coin _) _ = [(True, []), (False, [])]
    aux' (Lmap f x) b = aux x (f b)
    aux' (InternaliseMaybe x) b = case b of
      Nothing -> []
      Just a -> aux x a
    aux' (Label s x) b = second (s :) <$> aux x b

    aux :: FR b a -> b -> [(a, [String])]
    aux (Return x) _ = pure (x, [])
    aux (Bind mx f) b = do
      (x, cs) <- aux' mx b
      (y, cs') <- aux (f x) b
      pure (y, cs ++ cs')

data Tree = Leaf | Node Tree Int Tree
  deriving (Show, Eq, Ord)

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

reflPair :: FR a a -> FR b b -> FR (a, b) (a, b)
reflPair x y = (,) <$> lmap fst x <*> lmap snd y

reflInt :: (Int, Int) -> FR Int Int
reflInt (lo, hi) = pick [label (show i) (exact i) | i <- [lo .. hi]]

reflTree :: FR Tree Tree
reflTree = fix aux (10 :: Int)
  where
    aux self n
      | n == 0 = exact Leaf
      | otherwise = do
          pick
            [ exact Leaf,
              do
                x <- comap nodeValue (reflInt (1, 10))
                l <- comap nodeLeft (self (n - 1))
                r <- comap nodeRight (self (n - 1))
                pure (Node l x r),
              exact (Node Leaf 2 Leaf)
            ]

reflBSTpartial :: FR Void Tree
reflBSTpartial = aux (1, 10)
  where
    aux (lo, hi)
      | lo > hi = return Leaf
      | otherwise = do
          pick
            [ return Leaf,
              do
                x <- fwd (reflInt (lo, hi))
                l <- fwd (aux (lo, x - 1))
                r <- fwd (aux (x + 1, hi))
                return (Node l x r)
            ]

tryFocus :: Getting (First u') s u' -> FR u' v -> FR s v
tryFocus = comap . preview

focus :: Getting b s b -> FR b c -> FR s c
focus = lmap . view

reflBST :: FR Tree Tree
reflBST = fix aux (1, 10)
  where
    aux self (lo, hi)
      | lo > hi = exact Leaf
      | otherwise = do
          pick
            [ label "leaf" (exact Leaf),
              label "node" $ do
                x <- tryFocus (_Node . _2) (reflInt (lo, hi))
                l <- tryFocus (_Node . _1) (self (lo, x - 1))
                r <- tryFocus (_Node . _3) (self (x + 1, hi))
                exact (Node l x r)
            ]

hypoTree :: FR Tree Tree
hypoTree = do
  c <- coin 0.5
  if c
    then do
      l <- draw (comap nodeLeft hypoTree)
      r <- draw (comap nodeRight hypoTree)
      exact (Node l 0 r)
    else exact Leaf
  where
    draw = label ""

hypothesis :: FR a a -> a -> String
hypothesis g = map (\case True -> '1'; False -> '0') . head . bits g

data Expr
  = Num Int
  | Add Expr Expr
  | Mul Expr Expr
  deriving (Show, Eq, Ord)

makePrisms ''Expr

expr :: FR Expr Expr
expr =
  pick
    [ do
        x <- tryFocus (_Add . _1) term
        y <- token "+" *> tryFocus (_Add . _2) expr
        pure (Add x y),
      term
    ]
  where
    term =
      pick
        [ do
            x <- tryFocus (_Mul . _1) factor
            y <- token "*" *> tryFocus (_Mul . _2) term
            pure (Mul x y),
          factor
        ]
    factor =
      pick
        [ Num <$> tryFocus _Num (reflInt (1, 10)),
          token "(" *> expr <* token ")"
        ]
    token s = label s (pure ())

main :: IO ()
main = do
  print (nub $ bits reflTree (Node Leaf 1 (Node Leaf 2 Leaf)))
  print =<< QC.generate (gen reflTree)
  print =<< QC.generate (gen reflBSTpartial)
  let cs = head . nub $ bits reflBST (Node Leaf 1 (Node Leaf 2 Leaf))
  print cs
  print (regen reflBST cs)
  let ss = head . nub $ unparse reflBST (Node Leaf 1 (Node Leaf 2 Leaf))
  print ss
  print (parse reflBST ss)
  let n l = Node l 0
  putStrLn $ hypothesis hypoTree (n (n Leaf (n (n Leaf (n (n Leaf Leaf) Leaf)) Leaf)) (n (n Leaf (n (n Leaf (n Leaf Leaf)) (n Leaf Leaf))) Leaf))
  putStrLn $ hypothesis hypoTree (n Leaf (n (n Leaf (n (n Leaf (n Leaf Leaf)) (n Leaf Leaf))) Leaf))
  putStrLn $ hypothesis hypoTree (n Leaf (n (n Leaf Leaf) Leaf))
  putStrLn $ hypothesis hypoTree (n Leaf (n Leaf (n Leaf Leaf)))
  print $ choices hypoTree (n Leaf (n Leaf (n Leaf Leaf)))
  print $ choices reflBST (Node (Node Leaf 1 Leaf) 3 (Node Leaf 5 Leaf))
  let tii = (,,) <$> focus _1 reflBST <*> focus _2 (reflInt (1, 10)) <*> focus _3 (reflInt (1, 10)) :: FR (Tree, Int, Int) (Tree, Int, Int)
  mapM_ print $ take 20 $ nub $ enum tii
  print $ map fst $ filter (null . snd) $ parse expr (words "( 1 + 2 ) * ( 3 + 3 * 4 )")
  print $ take 3 $ map concat $ unparse expr (Mul (Add (Num 1) (Num 2)) (Num 3))