{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC  #-}
{-# OPTIONS_GHC -Wall #-}

module PartialProfunctors where

import Data.Profunctor (Profunctor (dimap))

class
  Profunctor p =>
  PartialProfunctor p
  where
  internaliseMaybe :: p u v -> p (Maybe u) v

dimap'' :: PartialProfunctor p => (u -> Maybe u') -> (v -> v') -> p u' v -> p u v'
dimap'' f g = dimap' f g . internaliseMaybe
  where
    dimap' :: Profunctor p => (u -> Maybe u') -> (v -> v') -> p (Maybe u') v -> p u v'
    dimap' = dimap

comap :: PartialProfunctor p => (u -> Maybe u') -> p u' v -> p u v
comap f = dimap'' f id

upon :: PartialProfunctor p => p u' v -> (u -> Maybe u') -> p u v
upon = flip comap

-- Note: this is like a natural transformation for a bifunctor P : C^op x C -> Set
--   internaliseMaybe :: P -> P . (Maybe x Id)

-- Perhaps this should satisfy something that looks a lot like monad algebra properties
-- Let a = internaliseMaybe and M = Maybe then
-- I think we should require

--                      a
--        P     ------------------> P . (M x Id)
--
--        |                           |
--      a |                           | P mu id
--        |                           |
--        v                           v

--    P . (M x Id)   ---------->   P . (M . M x Id)
--                      a M

--                 a
--        P -------------> P . (M x Id)
--        \                |
--         \               |  P eta id
--          \              |
--           \             v
--            -----------> P

-- The following is just to verify that these properties are well typed

_unit :: PartialProfunctor p => [p u v -> p u v]
_unit = [dimap return id . internaliseMaybe, id]

_assoc :: PartialProfunctor p => [p u v -> p (Maybe (Maybe u)) v]
_assoc = [dimap _join id . internaliseMaybe, internaliseMaybe . internaliseMaybe]

_join :: Maybe (Maybe a) -> Maybe a
_join = (>>= id)
