{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wall #-}

module UnGenFChoices where

import BidirectionalProfunctors (Profmonad)
import Control.Applicative (Alternative (..))
import Control.Arrow (first)
import Control.Monad.Writer
import Data.Foldable (Foldable (toList))
import Data.Profunctor (Profunctor (..))
import PartialProfunctors (PartialProfunctor (..))
import Reflective (Pick (..), Reflective)

data FChoices a
  = None
  | Mark a (FChoices a)
  | ASplit (FChoices a) (FChoices a)
  | MSplit (FChoices a) (FChoices a)
  | FanOut [FChoices a]

deriving instance Eq a => Eq (FChoices a)

deriving instance Ord a => Ord (FChoices a)

deriving instance Show a => Show (FChoices a)

instance Functor FChoices where
  fmap _ None = None
  fmap f (ASplit x y) = ASplit (f <$> x) (f <$> y)
  fmap f (MSplit x y) = MSplit (f <$> x) (f <$> y)
  fmap f (Mark x cs) = Mark (f x) (f <$> cs)
  fmap f (FanOut xs) = FanOut (fmap f <$> xs)

instance Foldable FChoices where
  foldMap _ None = mempty
  foldMap f (ASplit x y) = mappend (foldMap f x) (foldMap f y)
  foldMap f (MSplit x y) = mappend (foldMap f x) (foldMap f y)
  foldMap f (Mark a x) = mappend (f a) (foldMap f x)
  foldMap f (FanOut xs) = foldMap (foldMap f) xs

newtype UnGenFChoices t b a = UnGenFChoices {run :: b -> Maybe (a, FChoices t)}

instance Functor (UnGenFChoices t b) where
  fmap f x = UnGenFChoices $ fmap (first f) . run x

instance Applicative (UnGenFChoices t b) where
  pure = return
  mx <*> my = UnGenFChoices $ \b -> do
    (x, cs) <- run mx b
    (y, cs') <- run my b
    pure (x y, ASplit cs cs')

instance Monad (UnGenFChoices t b) where
  return x = UnGenFChoices $ const (pure (x, None))
  mx >>= f = UnGenFChoices $ \b -> do
    (x, cs) <- run mx b
    (y, cs') <- run (f x) b
    pure (y, MSplit cs cs')

instance Profunctor (UnGenFChoices t) where
  dimap bwd fwd x = fwd <$> UnGenFChoices (run x . bwd)

instance PartialProfunctor (UnGenFChoices t) where
  internaliseMaybe x = UnGenFChoices (run x <=< id)

instance Profmonad (UnGenFChoices t)

instance Alternative (UnGenFChoices t b) where
  empty = UnGenFChoices $ const Nothing
  ux <|> uy = UnGenFChoices (\b -> run ux b <|> run uy b)

instance Pick UnGenFChoices where
  pick xs =
    UnGenFChoices
      ( \b ->
          let fan = do
                (t, g) <- xs
                (x, ts) <- toList (run g b)
                return (x, Mark t ts)
           in case fan of
                [] -> Nothing
                [p] -> Just p
                ((x, _) : _) -> Just (x, FanOut (snd <$> fan))
      )

instance Reflective UnGenFChoices

unGenFChoices :: (forall g. Reflective g => g t a a) -> a -> Maybe (FChoices t)
unGenFChoices x a = snd <$> run x a
