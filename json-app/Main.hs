{-

Main file for application that recreates the IFH experiment. (Section 5.2)

-}
module Main (main) where

import Control.Monad (replicateM)
import Data.Bits (xor)
import Data.Foldable (Foldable (foldl'))
import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Data.String (fromString)
import Interps (generate, weightsFor, weighted)
import Examples.JSON (withChecksum)
import System.Directory (getDirectoryContents)
import qualified Test.QuickCheck as QC

hash :: (Foldable t, Enum a) => t a -> String
hash p = take 8 (show (abs (foldl' (\h c -> 33 * h `xor` fromEnum c) 5381 p)))

fixup :: String -> String
fixup s = "{\"payload\":" ++ s ++ ",\"checksum\":" ++ hash s ++ "}"

main :: IO ()
main = do
  files <- drop 2 <$> getDirectoryContents "analysis/json"
  let files' = filter (/= (fromString ".." ::FilePath)) files
  jsons <- mapM (readFile . ("analysis/json/" ++)) files'
  let w = weightsFor withChecksum (map fixup jsons)
  print w
  writeFile "analysis/weighted.json" . intercalate "\n" =<< replicateM 1000 (QC.generate (weighted withChecksum False (fromMaybe 0 . (`lookup` w))))
  writeFile "analysis/unweighted.json" . intercalate "\n" =<< replicateM 1000 (QC.generate (generate withChecksum))
