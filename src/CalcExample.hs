{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use isNothing" #-}

module CalcExample where

import Control.Lens (makePrisms, _1, _2)
import Data.Maybe (isJust)
import Freer (Reflective)
import qualified Freer as Reflective
import GHC.Generics (Generic)
import Test.QuickCheck
  ( Arbitrary (..),
    genericShrink,
  )

-- From SmartCheck

data Exp
  = C Int
  | Add Exp Exp
  | Div Exp Exp
  deriving (Show, Read, Generic, Eq)

makePrisms ''Exp

eval :: Exp -> Maybe Int
eval (C i) = Just i
eval (Add e0 e1) =
  (+) <$> eval e0 <*> eval e1
eval (Div e0 e1) =
  let e = eval e1
   in if e == Just 0
        then Nothing
        else div <$> eval e0 <*> e

instance Arbitrary Exp where
  arbitrary = Reflective.gen reflCalc -- Modified
  shrink = genericShrink

prop_div :: Exp -> Bool
prop_div e = not (divSubTerms e) || isJust (eval e)

divSubTerms :: Exp -> Bool
divSubTerms (C _) = True
divSubTerms (Div _ (C 0)) = False
divSubTerms (Add e0 e1) = divSubTerms e0 && divSubTerms e1
divSubTerms (Div e0 e1) = divSubTerms e0 && divSubTerms e1

-- Get the minimal offending sub-value.
findVal :: Exp -> (Exp, Exp)
findVal (Div e0 e1)
  | eval e1 == Just 0 = (e0, e1)
  | eval e1 == Nothing = findVal e1
  | otherwise = findVal e0
findVal a@(Add e0 e1)
  | eval e0 == Nothing = findVal e0
  | eval e1 == Nothing = findVal e1
  | eval a == Just 0 = (a, a)
findVal _ = error "not possible"

size :: Exp -> Int
size e = case e of
  C _ -> 1
  Add e0 e1 -> 1 + size e0 + size e1
  Div e0 e1 -> 1 + size e0 + size e1

-- Reflective Generator

reflCalc :: Reflective Exp Exp
reflCalc = Reflective.sized mkM
  where
    mkM 0 = C <$> Reflective.focus _C Reflective.integer
    mkM n =
      Reflective.frequency
        [ (1, C <$> Reflective.focus _C Reflective.integer),
          ( n - 1,
            Add
              <$> Reflective.focus (_Add . _1) (mkM (n `div` 2))
              <*> Reflective.focus (_Add . _2) (mkM (n `div` 2))
          ),
          ( n - 1,
            Div
              <$> Reflective.focus (_Div . _1) (mkM (n `div` 2))
              <*> Reflective.focus (_Div . _2) (mkM (n `div` 2))
          )
        ]
