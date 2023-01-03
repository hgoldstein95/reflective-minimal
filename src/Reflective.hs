{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeFamilies #-}

module Reflective where

import BidirectionalProfunctors (Profmonad)
import Control.Lens (Getting, Prism', preview)
import Control.Lens.Combinators (review)
import Data.Monoid (First)
import PartialProfunctors (PartialProfunctor, comap)

class Pick g where
  pick ::
    (Eq t, Eq a) =>
    [(t, g t a a)] ->
    g t a a

class
  ( forall t. Profmonad (g t),
    forall t. PartialProfunctor (g t),
    Pick g
  ) =>
  Reflective g

(<$$>) ::
  (PartialProfunctor p, Profmonad p) =>
  Prism' b a ->
  p a a ->
  p b b
(<**>) ::
  (PartialProfunctor p, Profmonad p) =>
  p a a ->
  p b b ->
  p (a, b) (a, b)
p <$$> x = fmap (review p) (comap (preview p) x)

infixr 0 <$$>

px <**> py = do
  x <- comap mfst px
  y <- comap msnd py
  return (x, y)
  where
    mfst (x, _) = Just x
    msnd (_, y) = Just y

infixl 4 <**>

at :: (PartialProfunctor p) => p u' v -> Getting (First u') u u' -> p u v
at x y = (comap . preview) y x

exact :: (Reflective g, Eq a) => a -> g t a a
exact x = comap (\y -> if y == x then Just y else Nothing) (pure x)
