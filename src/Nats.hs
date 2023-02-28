{-# LANGUAGE TemplateHaskell #-}

module Nats where

import Control.Lens (makePrisms)
import Freer

data Nat = Z | S Nat
  deriving (Eq, Ord, Show)

fromN :: Int -> Nat
fromN 0 = Z
fromN n = S (fromN (n - 1))

makePrisms ''Nat

g1 :: Reflective Nat Nat
g1 =
  labelled
    [ ("Z", exact Z),
      ("S", fmap S (focus _S g1))
    ]

gE :: Reflective Nat Nat
gE =
  labelled
    [ ("Z", exact Z),
      ("S", fmap S (focus _S gE)),
      ("2", fmap (S . S) (focus (_S . _S) gE))
    ]

gI :: Reflective Nat Nat
gI =
  labelled
    [ ("Z", exact Z),
      ("S", fmap S (focus _S gI)),
      ("∞", gI)
    ]