{-# LANGUAGE LambdaCase #-}

module Hypothesis where

import qualified Bound5Example as Bound5
import qualified CalcExample as Calc
import Control.Monad (replicateM)
import Freer (Reflective, gen, validate)
import qualified Freer
import qualified HeapExample as Heap
import qualified ListExample as List
import qualified ParserExample as Parser
import Test.QuickCheck
  ( Arbitrary (..),
    Args (chatty, maxShrinks, maxSize, maxSuccess),
    Result (Failure, failingTestCase),
    Testable (propertyForAllShrinkShow),
    quickCheckWithResult,
    shrinkNothing,
    stdArgs,
  )
import Text.Printf (printf)

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

counterExampleReflective :: (Eq a, Show a, Read a) => Reflective a a -> (a -> Bool) -> IO a
counterExampleReflective g p =
  quickCheckWithResult (stdArgs {chatty = False, maxSuccess = 10000, maxSize = 30, maxShrinks = 1}) (propertyForAllShrinkShow (gen g) (\v -> let v' = Freer.shrink (not . p) g v in [v' | v /= v']) ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleReflective: no counterexample found"

average :: [Int] -> Double
average xs = fromIntegral (sum xs) / fromIntegral (length xs)

stddev :: [Int] -> Double
stddev xs = sqrt (sum [(fromIntegral x - mean) ** 2 | x <- xs] / fromIntegral (length xs))
  where
    mean = average xs

experiment :: (Arbitrary a, Eq a, Show a, Read a) => (a -> Bool) -> (a -> Bool) -> Reflective a a -> (a -> Int) -> Int -> IO ()
experiment prop inv refl size n = do
  x <- measure $ counterExampleNone prop
  y <- measure $ counterExampleGeneric prop inv
  z <- measure $ counterExampleReflective refl prop
  putStrLn $ x ++ " & " ++ y ++ " & " ++ z
  where
    measure x = do
      xs <- replicateM n x
      let sizes = size <$> xs
      let mean = average sizes
      let dev = stddev sizes
      pure (printf "%.2f" mean ++ " (" ++ printf "%.2f" (max 0 (mean - 2 * dev)) ++ "--" ++ printf "%.2f" (mean + 2 * dev) ++ ")")

main :: IO ()
main = do
  validate Calc.reflCalc
  validate Heap.reflHeap
  validate (Freer.resize 10 Parser.reflLang) -- Size 30 is a bit slow
  validate Bound5.reflT

  let n = 1000

  putStr "heap: " >> experiment Heap.prop_ToSortedList Heap.invariant Heap.reflHeap Heap.size n
  putStr "bound5: " >> experiment Bound5.prop Bound5.pre Bound5.reflT Bound5.size n
  putStr "calc: " >> experiment Calc.prop_div Calc.divSubTerms Calc.reflCalc Calc.size n
  putStr "parser: " >> experiment Parser.prop_Parse Parser.invariant Parser.reflLang Parser.size n
  putStr "reverse: " >> experiment List.prop_Reverse List.invariant List.reflList List.size n