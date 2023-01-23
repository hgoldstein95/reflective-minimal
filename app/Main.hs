module Main (main) where

import qualified Bound5Example
import qualified CalcExample
import Freer (validate)
import qualified HeapExample
import qualified ListExample
import qualified ParserExample

main :: IO ()
main = do
  validate CalcExample.reflCalc
  validate HeapExample.reflHeap
  validate ParserExample.reflExp
  validate Bound5Example.reflT

  print =<< ListExample.main 1000
  print =<< CalcExample.main 1000
  print =<< HeapExample.main 1000
  print =<< ParserExample.main 100
  print =<< Bound5Example.main 1
