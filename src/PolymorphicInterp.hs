{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module PolymorphicInterp where

import Data.Profunctor (Profunctor (..))
import Freer hiding (lmap, prune)

class Profunctor p => PartialProf p where
  prune :: p b a -> p (Maybe b) a

interpret ::
  forall p d c.
  (PartialProf p, forall b. Monad (p b)) =>
  (forall b a. [(Weight, Choice, Reflective b a)] -> p b a) ->
  Reflective d c ->
  p d c
interpret p = interp
  where
    interp :: forall b a. Reflective b a -> p b a
    interp (Return a) = return a
    interp (Bind r f) = do
      a <- interpR r
      interpret p (f a)

    interpR :: forall b a. R b a -> p b a
    interpR (Pick xs) = p xs
    interpR (Lmap f r) = lmap f (interpR r)
    interpR (Prune r) = prune (interpR r)
    interpR _ = error "interpret: impossible"