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

  print =<< HeapExample.main 100
  print =<< Bound5Example.main 100
  print =<< CalcExample.main 100
  print =<< ParserExample.main 100
  print =<< ListExample.main 100
