module Main (main) where

import Data.List (isInfixOf)
import Freer (shrink)
import PackageJSONExample (package)

main :: IO ()
main = getContents >>= putStrLn . shrink (isInfixOf "\"express\":\"^4.15.3\"") package