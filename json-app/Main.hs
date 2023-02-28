module Main (main) where

import Control.Monad (replicateM)
import Data.Bits (xor)
import Data.Foldable (Foldable (foldl'))
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Freer (generate, probabilityOf, weighted)
import JSONExample (withChecksum)
import System.Directory (getDirectoryContents)
import qualified Test.QuickCheck as QC

hash p = take 8 (show (abs (foldl' (\h c -> 33 * h `xor` fromEnum c) 5381 p)))

fixup s = "{\"payload\":" ++ s ++ ",\"checksum\":" ++ hash s ++ "}"

main :: IO ()
main = do
  files <- drop 2 <$> getDirectoryContents "analysis/json"
  jsons <- mapM (readFile . ("analysis/json/" ++)) files
  let w = probabilityOf withChecksum (map fixup jsons)
  print w
  writeFile "analysis/weighted.json" . intercalate "\n" =<< replicateM 1000 (QC.generate (weighted withChecksum False (fromMaybe 0 . (`lookup` w))))
  writeFile "analysis/unweighted.json" . intercalate "\n" =<< replicateM 1000 (QC.generate (generate withChecksum))
