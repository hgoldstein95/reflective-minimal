{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use isNothing" #-}

module CalcExample where

import Control.Lens (makePrisms, _1, _2)
import Control.Monad (replicateM)
import Data.Maybe (isJust)
import Freer (FR)
import qualified Freer as FR
import GHC.Generics (Generic)
import Test.QuickCheck
  ( Arbitrary (..),
    Args (chatty, maxShrinks, maxSize, maxSuccess),
    Result (Failure, failingTestCase),
    Testable (propertyForAllShrinkShow),
    frequency,
    genericShrink,
    quickCheckWithResult,
    shrinkNothing,
    sized,
    stdArgs,
  )

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

reflCalc :: FR Exp Exp
reflCalc = FR.sized mkM
  where
    mkM 0 = C <$> FR.tryFocus _C FR.integer
    mkM n =
      FR.frequency
        [ (1, C <$> FR.tryFocus _C FR.integer),
          ( n - 1,
            Add
              <$> FR.tryFocus (_Add . _1) (mkM (n `div` 2))
              <*> FR.tryFocus (_Add . _2) (mkM (n `div` 2))
          ),
          ( n - 1,
            Div
              <$> FR.tryFocus (_Div . _1) (mkM (n `div` 2))
              <*> FR.tryFocus (_Div . _2) (mkM (n `div` 2))
          )
        ]

instance Arbitrary Exp where
  arbitrary = sized mkM
    where
      mkM 0 = C <$> arbitrary
      mkM n =
        frequency
          [ (1, C <$> arbitrary),
            (n - 1, Add <$> mkM (n `div` 2) <*> mkM (n `div` 2)),
            (n - 1, Div <$> mkM (n `div` 2) <*> mkM (n `div` 2))
          ]
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

counterExampleNone :: (Show a, Read a, Arbitrary a) => (a -> Bool) -> IO a
counterExampleNone p =
  quickCheckWithResult (stdArgs {chatty = False, maxSuccess = 10000}) (propertyForAllShrinkShow arbitrary shrinkNothing ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleNone: no counterexample found"

counterExampleGeneric :: (Show a, Read a, Arbitrary a) => (a -> Bool) -> (a -> Bool) -> IO a
counterExampleGeneric p inv =
  quickCheckWithResult (stdArgs {chatty = False, maxSuccess = 10000}) (propertyForAllShrinkShow arbitrary (filter inv . shrink) ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleGeneric: no counterexample found"

counterExampleFR :: (Eq a, Show a, Read a) => FR a a -> (a -> Bool) -> IO a
counterExampleFR g p =
  quickCheckWithResult (stdArgs {chatty = False, maxSuccess = 10000, maxSize = 30, maxShrinks = 1}) (propertyForAllShrinkShow (FR.gen g) (\v -> let v' = FR.shrink (not . p) g v in [v' | v /= v']) ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleFR: no counterexample found"

average :: [Int] -> Double
average xs = fromIntegral (sum xs) / fromIntegral (length xs)

main :: Int -> IO (Double, Double, Double)
main n = do
  putStr "calc: "
  x <- measure $ counterExampleNone prop_div
  y <- measure $ counterExampleGeneric prop_div divSubTerms
  z <- measure $ counterExampleFR reflCalc prop_div
  pure (x, y, z)
  where
    measure x = do
      xs <- replicateM n x
      pure (average (size <$> xs))