{-# HLINT ignore "Eta reduce" #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module FR where

import BidirectionalProfunctors (Profmonad)
import Control.Applicative (Alternative (..))
import Control.Arrow (first)
import Control.Monad ((<=<))
import Data.Foldable (Foldable (toList), asum)
import Data.Profunctor (Profunctor (..))
import HedgehogTree (TreeT)
import PartialProfunctors (PartialProfunctor (..))
import Test.QuickCheck (Gen)
import qualified Test.QuickCheck as QC
import UnGenFChoices (FChoices (..))

data FR t b a where
  Return :: a -> FR t b a
  Dimap :: (c -> d) -> (a -> b) -> FR t d a -> FR t c b
  Magic :: FR t c a -> FR t b a
  Ap :: FR t b (a -> c) -> FR t b a -> FR t b c
  Bind :: FR t b a -> (a -> FR t b c) -> FR t b c
  Pick :: t -> [FR t a a] -> FR t a a
  InternaliseMaybe :: FR t b a -> FR t (Maybe b) a
  Fix :: ((i -> FR t b a) -> i -> FR t b a) -> i -> FR t b a

magic :: FR t c a -> FR t b a
magic = Magic

fix :: ((i -> FR t b a) -> i -> FR t b a) -> i -> FR t b a
fix = Fix

relabel :: forall t t' a b. (t -> t') -> FR t b a -> FR t' b a
relabel change = run
  where
    run :: forall c d. FR t c d -> FR t' c d
    run (Magic x) = Magic (run x)
    run (Return x) = Return x
    run (Dimap bwd fwd x) = Dimap bwd fwd (run x)
    run (Ap x y) = Ap (run x) (run y)
    run (Bind x f) = Bind (run x) (run . f)
    run (Pick s xs) = Pick (change s) (map run xs)
    run (InternaliseMaybe x) = InternaliseMaybe (run x)
    run Fix {} = error "relabel: Fix"

gen :: FR t a a -> Gen a
gen g = run g
  where
    run :: FR t b a -> Gen a
    run (Magic x) = run x
    run (Return x) = pure x
    run (Dimap _ fwd x) = fwd <$> run x
    run (Ap x y) = run x <*> run y
    run (Bind x f) = do
      y <- run x
      run (f y)
    run (Pick _ xs) = QC.oneof (map run xs)
    run (InternaliseMaybe x) = run x
    run (Fix f i) = run (f (Fix f) i)

small :: FR t a a -> [a]
small g = aux 0
  where
    aux i = case run g i of
      [] -> aux (i + 1)
      xs -> xs
    run :: FR t b a -> Int -> [a]
    run (Magic x) i = run x i
    run (Return x) _ = pure x
    run (Dimap _ fwd x) i = fwd <$> run x i
    run (Ap x y) i = run x i <*> run y i
    run (Bind x f) i = do
      y <- run x i
      run (f y) i
    run (Pick _ xs) i
      | i <= 0 = []
      | otherwise = do
          x <- xs
          run x (i - 1)
    run (InternaliseMaybe x) i = run x i
    run (Fix f i) b = run (f (Fix f) i) b

shrink :: FR t a a -> a -> [a]
shrink g a = toList (run g a)
  where
    run :: FR t b a -> b -> TreeT [] a
    run (Magic _) _ = error "shrink: Magic"
    run (Return x) _ = pure x
    run (Dimap bwd fwd x) b = fwd <$> run x (bwd b)
    run (Ap x y) i = run x i <*> run y i
    run (Bind x f) b = do
      y <- run x b
      run (f y) b
    run (Pick _ xs) b = asum $ do
      x <- xs
      pure (run x b)
    run (InternaliseMaybe x) b = case b of
      Nothing -> empty
      Just b' -> run x b'
    run (Fix f i) b = run (f (Fix f) i) b

choices :: FR String a a -> a -> [FChoices String]
choices rg a = snd <$> run rg a
  where
    run :: FR String b a -> b -> [(a, FChoices String)]
    run (Magic _) _ = error "choices: Magic"
    run (Return x) _ = [(x, None)]
    run (Dimap bwd fwd x) b = first fwd <$> run x (bwd b)
    run (Ap mx my) b = do
      (x, cs) <- run mx b
      (y, cs') <- run my b
      pure (x y, ASplit cs cs')
    run (Bind mx f) b = do
      (x, cs) <- run mx b
      (y, cs') <- run (f x) b
      pure (y, MSplit cs cs')
    run (Pick t xs) b = do
      (i, g) <- zip [(0 :: Int) ..] xs
      (x, ts) <- run g b
      return (x, Mark (t ++ "." ++ show i) ts)
    run (InternaliseMaybe x) b = (run x <=< toList) b
    run (Fix f i) b = run (f (Fix f) i) b

instance Functor (FR t b) where
  fmap f (Return a) = Return (f a)
  fmap f x = dimap id f x

instance Applicative (FR t b) where
  pure = return
  Return f <*> y = f <$> y
  x <*> Return a = ($ a) <$> x
  x <*> y = Ap x y

instance Profmonad (FR t)

instance Monad (FR t b) where
  return = Return
  Return a >>= f = f a
  x >>= f = Bind x f

pick :: t -> [FR t a a] -> FR t a a
pick = Pick

instance Profunctor (FR t) where
  dimap _ g (Return a) = Return (g a)
  dimap f g x = Dimap f g x

instance PartialProfunctor (FR t) where
  internaliseMaybe = InternaliseMaybe
