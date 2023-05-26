{-

Main file for application that compares Reflective Generator shrinking to that of
  - Hypothesis
  - QuickCheck’s genericShrink
  - un-shrunk inputs
by recreating the experiments from the Hypothesis paper. (Table 1).

The output is printed to the terminal in format:
  "experiment: unshrink mean (unshrink stddev range)
           & QC.genericShrink mean (QC.genericShrink stddev range)
           & reflective mean (reflective stddev range)"

Note that the Hypothesis numbers in the paper are not re-run, but taken directly from their experiment.
Note also that this experiment is slow.

-}

module Main (main) where

import qualified Examples.Hypothesis

main :: IO ()
main = Examples.Hypothesis.main
