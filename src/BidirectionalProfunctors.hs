{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module BidirectionalProfunctors where

import Data.Profunctor (Profunctor (dimap))

class (Profunctor p, forall u. Monad (p u)) => Profmonad p

newtype Fwd m u v = Fwd {unFwd :: m v}

newtype Bwd m u v = Bwd {unBwd :: u -> m v}

instance Functor m => Functor (Fwd m u) where
  fmap f (Fwd m) = Fwd $ fmap f m

instance Functor m => Profunctor (Fwd m) where
  dimap _ fwf (Fwd mx) = Fwd (fmap fwf mx)

instance Monad m => Monad (Fwd m u) where
  return x = Fwd (return x)
  Fwd py >>= kz = Fwd (py >>= unFwd . kz)

instance Monad m => Applicative (Fwd m u) where
  pure = return
  mf <*> mx = mf >>= (<$> mx)

instance Functor m => Functor (Bwd m u) where
  fmap f (Bwd m) = Bwd $ (f <$>) . m

instance Functor m => Profunctor (Bwd m) where
  dimap bwf fwf (Bwd kx) = Bwd ((fwf <$>) . kx . bwf)

instance Monad m => Monad (Bwd m u) where
  return x = Bwd (\_ -> return x)
  Bwd my >>= kz = Bwd (\u -> my u >>= (\y -> unBwd (kz y) u))

instance Monad m => Applicative (Bwd m u) where
  pure = return
  mf <*> mx = mf >>= (<$> mx)

data (:*:) p q u v = (:*:) {pfst :: p u v, psnd :: q u v}

instance (Functor (p u), Functor (q u)) => Functor ((p :*: q) u) where
  fmap f (p :*: q) = fmap f p :*: fmap f q

instance
  (Profunctor p, Profunctor q) =>
  Profunctor (p :*: q)
  where
  dimap fwf bwf (py :*: qy) = dimap fwf bwf py :*: dimap fwf bwf qy

instance (Profunctor p, Profunctor q, Monad (p u), Monad (q u)) => Monad ((p :*: q) u) where
  return y = return y :*: return y
  py :*: qy >>= kz = (py >>= pfst . kz) :*: (qy >>= psnd . kz)

instance (Profunctor p, Profunctor q, Monad (p u), Monad (q u)) => Applicative ((p :*: q) u) where
  pure = return
  mf <*> mx = mf >>= (<$> mx)

instance (Profmonad p, Profmonad q) => Profmonad (p :*: q)
