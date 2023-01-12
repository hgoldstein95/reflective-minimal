{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# HLINT ignore "Eta reduce" #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module HedgehogTree where

import Control.Applicative (Alternative (..))
import Control.Monad (ap)

newtype TreeT m a = TreeT {runTreeT :: m (NodeT m a)}
  deriving (Functor)

data NodeT m a = NodeT {nodeValue :: a, nodeChildren :: [TreeT m a]}
  deriving (Functor)

instance Monad m => Applicative (TreeT m) where
  pure = return
  (<*>) = ap

instance Monad m => Applicative (NodeT m) where
  pure = return
  (<*>) = ap

instance Monad m => Monad (NodeT m) where
  return x = NodeT x []

  (>>=) (NodeT x xs) k =
    let NodeT y ys = k x
     in NodeT y $ fmap (TreeT . fmap (>>= k) . runTreeT) xs ++ ys

instance Monad m => Monad (TreeT m) where
  return = TreeT . pure . pure

  (>>=) m k =
    TreeT $ do
      NodeT x xs <- runTreeT m
      NodeT y ys <- runTreeT (k x)
      pure . NodeT y $
        fmap (>>= k) xs ++ ys

instance (Monad m, Alternative m) => Alternative (TreeT m) where
  empty = TreeT empty
  (<|>) x y = TreeT (runTreeT x <|> runTreeT y)

instance Foldable (TreeT []) where
  foldMap f (TreeT mx) =
    foldMap (foldMap f) mx

instance Foldable (NodeT []) where
  foldMap f (NodeT x xs) =
    f x `mappend` mconcat (fmap (foldMap f) xs)