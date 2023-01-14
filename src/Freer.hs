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
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Freer2 where

import BidirectionalProfunctors (Profmonad)
import Control.Exception (SomeException)
import Control.Lens (Getting, makePrisms, preview, view, _1, _2, _3)
import Control.Monad (ap, (>=>))
import Control.Monad.Logic (Logic, MonadLogic ((>>-)), observeAll)
import Data.Bifunctor (Bifunctor (second))
import Data.Foldable (asum)
import Data.List (nub)
import Data.Maybe (catMaybes)
import Data.Monoid (First)
import Data.Profunctor (Profunctor (..))
import Data.Ratio (denominator, numerator)
import Data.Void (Void)
import GHC.IO (catch, evaluate)
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
  Sized :: (Int -> FR b a) -> Refl b a
  Resize :: Int -> FR b a -> Refl b a

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

label :: String -> FR b a -> FR b a
label s x = Bind (Label s x) Return

draw :: FR b a -> FR b a
draw = label ""

sized :: (Int -> FR b a) -> FR b a
sized f = Bind (Sized f) Return

resize :: Int -> FR b a -> FR b a
resize n x = Bind (Resize n x) Return

tryFocus :: Getting (First u') s u' -> FR u' v -> FR s v
tryFocus = comap . preview

focus :: Getting b s b -> FR b c -> FR s c
focus = lmap . view

gen :: FR b a -> Gen a
gen = aux
  where
    aux' (Coin w) = (< numerator w) <$> QC.choose (0, denominator w)
    aux' (Lmap _ x) = aux x
    aux' (InternaliseMaybe x) = aux x
    aux' (Label _ x) = aux x
    aux' (Sized f) = QC.sized (aux . f)
    aux' (Resize n x) = QC.resize n (aux x)

    aux :: FR b a -> Gen a
    aux (Return x) = pure x
    aux (Bind x f) = do
      y <- aux' x
      aux (f y)

byExample :: FR a a -> [a] -> Gen a
byExample g v = aux g v >>= QC.elements
  where
    aux' (Coin _) _ = pure [True, False]
    aux' (Lmap f x) b = aux x (f <$> b)
    aux' (InternaliseMaybe x) b = case catMaybes b of
      [] -> pure []
      bs -> aux x bs
    aux' (Label _ x) b = aux x b
    aux' (Sized f) b = aux (f 0) b
    aux' (Resize _ x) b = aux x b

    aux :: FR b a -> [b] -> Gen [a]
    aux (Return x) _ = pure (pure x)
    aux (Bind mx f) b = do
      x <- aux' mx b
      concat <$> mapM (\a -> aux (f a) b) x

enum :: FR b a -> [a]
enum = observeAll . aux
  where
    aux' (Coin w) = (< numerator w) <$> asum (map pure [0 .. denominator w])
    aux' (Lmap _ x) = aux x
    aux' (InternaliseMaybe x) = aux x
    aux' (Label _ x) = aux x
    aux' (Sized f) = aux (f 0)
    aux' (Resize _ x) = aux x

    aux :: FR b a -> Logic a
    aux (Return x) = pure x
    aux (Bind x f) =
      aux' x >>- \y ->
        aux (f y)

regen :: FR b a -> Bits -> [a]
regen rg cs = fst <$> aux rg (unBits cs)
  where
    aux' (Coin _) [] = []
    aux' (Coin _) (b : bs) = pure (b, bs)
    aux' (Lmap _ x) b = aux x b
    aux' (InternaliseMaybe x) b = aux x b
    aux' (Label _ x) b = aux x b
    aux' (Sized f) b = aux (f 0) b
    aux' (Resize _ x) b = aux x b

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
    aux' (Sized f) b = aux (f 0) b
    aux' (Resize _ x) b = aux x b

    aux :: FR b a -> [String] -> [(a, [String])]
    aux (Return x) b = pure (x, b)
    aux (Bind mx f) b = do
      (x, b') <- aux' mx b
      aux (f x) b'

newtype Bits = Bits {unBits :: [Bool]}
  deriving (Eq, Ord)

instance Show Bits where
  show (Bits bs) = concatMap (\b -> if b then "1" else "0") bs

bits :: FR a a -> a -> [Bits]
bits rg v = Bits . snd <$> aux rg v
  where
    aux' :: Refl b a -> b -> [(a, [Bool])]
    aux' (Coin _) _ = [(True, [True]), (False, [False])]
    aux' (Lmap f x) b = aux x (f b)
    aux' (InternaliseMaybe x) b = case b of
      Nothing -> []
      Just a -> aux x a
    aux' (Label _ x) b = aux x b
    aux' (Sized f) b = aux (f 0) b
    aux' (Resize _ x) b = aux x b

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
    aux' (Sized f) b = aux (f 0) b
    aux' (Resize _ x) b = aux x b

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
    aux' (Sized f) b = aux (f 0) b
    aux' (Resize _ x) b = aux x b

    aux :: FR b a -> b -> [(a, [String])]
    aux (Return x) _ = pure (x, [])
    aux (Bind mx f) b = do
      (x, cs) <- aux' mx b
      (y, cs') <- aux (f x) b
      pure (y, cs ++ cs')

complete :: FR a a -> a -> IO a
complete g v = aux g v 30 >>= QC.generate . QC.elements
  where
    aux' :: Refl b a -> b -> Int -> IO [a]
    aux' (Coin _) _ _ = pure [True, False]
    aux' (Lmap f x) b s = do
      catch
        (evaluate (f b) >>= \a -> aux x a s)
        (\(_ :: SomeException) -> (: []) <$> QC.generate (QC.resize s (gen x)))
    aux' (InternaliseMaybe x) b s = case b of
      Nothing -> pure []
      Just a -> aux x a s
    aux' (Label _ x) b s = aux x b s
    aux' (Sized f) b s = aux (f s) b s
    aux' (Resize s x) b _ = aux x b s

    aux :: FR b a -> b -> Int -> IO [a]
    aux (Return x) _ _ = pure [x]
    aux (Bind mx f) b s = do
      xs <- aux' mx b s
      concat <$> mapM (\x -> aux (f x) b s) xs

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

choose :: (Int, Int) -> FR Int Int
choose (lo, hi) = pick [label (show i) (exact i) | i <- [lo .. hi]]

weirdTree :: FR Tree Tree
weirdTree = sized aux
  where
    aux n
      | n == 0 = exact Leaf
      | otherwise = do
          pick
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
          pick
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
          pick
            [ label "leaf" (exact Leaf),
              label "node" $ do
                x <- tryFocus (_Node . _2) (choose (lo, hi))
                l <- tryFocus (_Node . _1) (aux (lo, x - 1))
                r <- tryFocus (_Node . _3) (aux (x + 1, hi))
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
        [ Num <$> tryFocus _Num (choose (1, 10)),
          token "(" *> expr <* token ")"
        ]
    token s = label s (pure ())

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
  let tii = (,,) <$> focus _1 bst <*> focus _2 (choose (1, 10)) <*> focus _3 (choose (1, 10)) :: FR (Tree, Int, Int) (Tree, Int, Int)
  mapM_ print $ take 20 $ nub $ enum tii
  print $ map fst $ filter (null . snd) $ parse expr (words "( 1 + 2 ) * ( 3 + 3 * 4 )")
  print $ take 3 $ map concat $ unparse expr (Mul (Add (Num 1) (Num 2)) (Num 3))
  let _hole_ = undefined
  print =<< complete bst (Node _hole_ 5 _hole_)
  print =<< complete bst (Node (Node _hole_ 2 Leaf) 5 (Node _hole_ 7 _hole_))
  print =<< QC.generate (byExample bst [Node Leaf 1 Leaf, Node Leaf 2 (Node Leaf 6 Leaf), Node Leaf 3 Leaf])