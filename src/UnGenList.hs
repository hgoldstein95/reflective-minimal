{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}

module UnGenList where

import BidirectionalProfunctors (Profmonad)
import Control.Applicative (Alternative (..))
import Control.Arrow (first)
import Control.Monad.Writer
import Data.Foldable (Foldable (toList))
import Data.Profunctor (Profunctor (..))
import PartialProfunctors (PartialProfunctor (..))
import Reflective (Pick (..), Reflective)

newtype UnGenList t b a = UnGenList {run :: b -> [(a, [t])]}

instance Functor (UnGenList t b) where
  fmap f x = UnGenList $ fmap (first f) . run x

instance Applicative (UnGenList t b) where
  pure = return
  (<*>) = ap

instance Profmonad (UnGenList t)

instance Alternative (UnGenList t b) where
  empty = UnGenList $ const mempty
  ux <|> uy = UnGenList (\b -> run ux b <|> run uy b)

instance Monad (UnGenList t b) where
  return x = UnGenList $ const (pure (x, []))
  mx >>= f = UnGenList $ \b -> do
    (x, cs) <- run mx b
    (y, cs') <- run (f x) b
    pure (y, cs ++ cs')

instance Pick UnGenList where
  pick xs =
    UnGenList
      ( \b -> do
          (t, g) <- xs
          (x, ts) <- run g b
          return (x, t : ts)
      )

instance Profunctor (UnGenList t) where
  dimap bwd fwd x =
    fwd <$> UnGenList (run x . bwd)

instance PartialProfunctor (UnGenList t) where
  internaliseMaybe x =
    UnGenList (run x <=< toList)

instance Reflective UnGenList

unGenList ::
  (forall g. Reflective g => g t a a) ->
  a ->
  [[t]]
unGenList x a = snd <$> run x a
