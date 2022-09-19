{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module GenList where

import BidirectionalProfunctors (Profmonad)
import Control.Monad (ap)
import Data.Foldable (find)
import Data.Profunctor (Profunctor (..))
import PartialProfunctors (PartialProfunctor (..))
import Reflective (Pick (..), Reflective)

newtype MutGen t b a = MutGen {run :: [t] -> Maybe (a, [t])}

fromChoices :: MutGen t a a -> [t] -> Maybe a
fromChoices g = fmap fst . run g

instance Functor (MutGen t b) where
  fmap f x = MutGen $ \ts -> do
    (a, xs') <- run x ts
    pure (f a, xs')

instance Applicative (MutGen t b) where
  pure = return
  (<*>) = ap

instance Monad (MutGen t b) where
  return a = MutGen $ \ts -> Just (a, ts)
  x >>= f = MutGen $ \ts -> do
    (y, ts') <- run x ts
    run (f y) ts'

instance Profunctor (MutGen t) where
  dimap _ fwd x = fwd <$> MutGen (run x)

instance PartialProfunctor (MutGen t) where
  internaliseMaybe = MutGen . run

instance Profmonad (MutGen t)

instance Pick MutGen where
  pick gs = MutGen $ \case
    (t : ts) -> do
      g <- snd <$> find ((== t) . fst) gs
      run g ts
    [] -> Nothing

instance Reflective MutGen
