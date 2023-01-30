module Main (main) where

import Data.List (isInfixOf)
import Freer hiding (main)
import JSONExample

main :: IO ()
main = getContents >>= putStrLn . shrink (isInfixOf "^4.15.3") package
