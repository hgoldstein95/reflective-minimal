{-# LANGUAGE LambdaCase #-}

module Hypothesis where

import qualified Bound5Example as Bound5
import qualified CalcExample as Calc
import Control.Monad (replicateM)
import Freer (Reflective, generate, validate)
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
  quickCheckWithResult (stdArgs {chatty = False, maxSuccess = 10000, maxSize = 30, maxShrinks = 1}) (propertyForAllShrinkShow (generate g) (\v -> let v' = Freer.shrink (not . p) g v in [v' | v /= v']) ((: []) . show) p) >>= \case
    Failure {failingTestCase = [v]} -> pure (read v)
    _ -> error "counterExampleReflective: no counterexample found"

average :: [Int] -> Double
average xs = fromIntegral (sum xs) / fromIntegral (length xs)

stddev :: [Int] -> Double
stddev xs = sqrt (sum [(fromIntegral x - mean) ** 2 | x <- xs] / fromIntegral (length xs))
  where
    mean = average xs

experiment :: (Arbitrary a, Eq a, Show a, Read a) => String -> (a -> Bool) -> (a -> Bool) -> Reflective a a -> (a -> Int) -> Int -> IO ()
experiment name prop inv refl size n = do
  putStr (name ++ ": ")
  writeFile fname "generator,size\n"
  x <- measure Nothing $ counterExampleNone prop
  y <- measure (Just "generic") $ counterExampleGeneric prop inv
  z <- measure (Just "reflective") $ counterExampleReflective refl prop
  putStrLn $ x ++ " & " ++ y ++ " & " ++ z
  where
    fname = "analysis/shrinks/" ++ name ++ "-shrink-sizes.csv"
    measure gname x = do
      xs <- replicateM n x
      let sizes = size <$> xs
      case gname of
        Just gn -> mapM_ (appendFile fname) [gn ++ "," ++ show s ++ "\n" | s <- sizes]
        Nothing -> pure ()
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

  experiment "heap" Heap.prop_ToSortedList Heap.invariant Heap.reflHeap Heap.size n
  experiment "bound5" Bound5.prop Bound5.pre Bound5.reflT Bound5.size n
  experiment "calc" Calc.prop_div Calc.divSubTerms Calc.reflCalc Calc.size n
  experiment "parser" Parser.prop_Parse Parser.invariant Parser.reflLang Parser.size n
  experiment "reverse" List.prop_Reverse List.invariant List.reflList List.size n