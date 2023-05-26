{-

Interpretation of a Reflective Generator as a generic PMP.

As a Reflective Generator is a syntactic representation of the partial monadic
profunctor operations, plus Pick, if the user can provide how Pick should be
interpreted in a PMP, Reflective Generators can be interpreted in any PMP in this
"polymorphic" interpretation.

-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}

module PolymorphicInterp where

import Data.Profunctor (Profunctor (..))
import Reflectives hiding (lmap, prune)

-- | Describes a partial profunctor by adding the prune operation to a profunctor.
class Profunctor p => PartialProf p where
  prune :: p b a -> p (Maybe b) a

-- | Polymorphic interpretation.
interpret
  :: forall p d c. (PartialProf p, forall b. Monad (p b))
  => (forall b a. [(Weight, Choice, Reflective b a)] -> p b a) -- ^ How to interpret Pick
  -> Reflective d c                                            -- ^ The generator to interpret
  -> p d c                                                     -- ^ Its interpretation
interpret p = interp
  where
    -- Interpret monadic syntax as PMP's monadic ops
    interp :: forall b a. Reflective b a -> p b a
    interp (Return a) = return a
    interp (Bind r f) = do
      a <- interpR r
      interpret p (f a)

    interpR :: forall b a. R b a -> p b a
    interpR (Pick  xs) = p xs -- Use the provided op to interpret Pick
    -- Interpret partial profunctor syntax as PMP's partial profunctor ops
    interpR (Lmap f r) = lmap f (interpR r)
    interpR (Prune  r) = prune (interpR r)
    interpR _ = error "interpret: impossible"