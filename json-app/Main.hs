module Main (main) where

import Control.Monad (replicateM)
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Freer (gen, weighted, weights)
import JSONExample (start)
import System.Directory (getDirectoryContents)
import Test.QuickCheck (generate)

main :: IO ()
main = do
  files <- drop 2 <$> getDirectoryContents "analysis/json"
  jsons <- mapM (readFile . ("analysis/json/" ++)) files
  let w = weights start jsons
  writeFile "analysis/weighted.json" . intercalate "\n" =<< replicateM 100 (generate (weighted start False (fromMaybe 0 . (`lookup` w))))
  writeFile "analysis/unweighted.json" . intercalate "\n" =<< replicateM 100 (generate (gen start))
